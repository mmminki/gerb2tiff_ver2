/*
File:	 	main.cpp
Author: 	Adam Seychell
Description:  main function for gerb2tiff program.


	copyright (c), 2001 Adam Seychell.

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

*/

#include <time.h>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <vector>
#include <list>
#include <map>
#include <string>
#include <math.h>
#include <limits.h>
#include <ctype.h>
#include <getopt.h>
#include <tiffio.h>
#include <stdarg.h>
#include <string.h>
#include "config.h"

using namespace std;

#include "polygon.h"
#include "apertures.h"
#include "gerber.h"

// 디버깅용 전역 포인터
unsigned char * DEGUB_bitmap_ptr_end;

// LUT (Look-Up Table) 생성: 각 값(0~255)의 활성 비트 수를 저장
unsigned char nbitsTable[256];

//PACKAGE_VERSION이 문자열로 확장되지 않고 사용자 정의 리터럴처럼 처리되어 " PACKAGE_VERSION " 공백 수정.
const char *help_message=
"gerb2tiff  version " PACKAGE_VERSION " Copyright (c) 2010 by Adam Seychell\n"
"Gerber RS-274X file to raster graphics converter \n"
"\n"
"Usage: gerb2tiff [OPTIONS] [file1] [file2]...\n"
"\n"
"Output control: \n"
"  -a, --area           Show total dark area of TIFF in square centimeters.\n"
"  -q, --quiet          Suppress warnings and non critical messages.\n"
"  -t                   Test only. Process Gerber file without writing TIFF.\n"
"  -o, --output=FILE    Set name of output TIFF to FILE. If gerber-file is\n"
"                       specified then default is <file1>.tiff\n"
"                       This option is required when no gerber-file specified.\n"
"  -v                   Verbose mode, display information while processing\n"
"                       multiple -v increases verbosity. Disables --quiet\n"
"  --help               This help screen\n"
"\n"
"Image options: \n"
"  --boarder-pixels=X   Add a boarder of X pixels around image. Default 0\n"
"  -b, --boarder-mm=X   same as --boarder except X is in millimeters\n"
"  -p, --dpi=X          Number of dots per inch X. Default 2400\n"
"  -n, --negative       Negate image polarity\n"
"  --grow-pixels=X      Expand perimeter of all aperture features by X pixels.\n"
"                       Negative values shrink. Fractional pixels allowed.\n"
"  --grow-mm=X          Same as --grow-pixels except X is in unit millimeters.\n"
"  --strip-rows=N       Specify N rows per strip in TIFF. Default 512\n"
"  --scale-y=FACTOR     Scale image in Y axis by FACTOR. Default 1\n"
"  --scale-x=FACTOR     Scale image in X axis by FACTOR. Default 1\n"
"\n"
"Where file1 file2... are gerber files rendered as overlays to a single bitmap.\n"
"Standard input is read if no gerber files specified and --output is specified.\n"
"Output bitmap is compressed monochrome TIFF.\n"
"\n"
"For latest releases and report bugs visit gerb2tiff home page at:\n"
" http://members.optusnet.com.au/eseychell\n";




// 특정 작업의 시간 측정 및 출력
void show_interval(const char * msg="")
{
	static clock_t  start_clock = clock();
    double cpu_time_used = ((double) (clock() - start_clock)) / CLOCKS_PER_SEC;
	printf("time: %.3f s (%s)\n",cpu_time_used,  msg);
	start_clock = clock();
}

// 오류 메시지를 출력하고 프로그램을 종료
void error(const string &message)
{
	cerr << "gerb2tiff: error: "<<message<<endl;
    exit(1);
}


//***************************************************
// Global variables of plotting parameters
//**************************************************

	// 전역 설정 변수 선언
	double imageDPI = 2400;                     // DPI 설정 (기본값 2400)
	double optRotation;                         // 이미지 회전
	bool optGrowUnitsMillimeters = false;       // Grow 옵션 단위 (mm 여부)
	bool optBoarderUnitsMillimeters = false;    // 보더 옵션 단위 (mm 여부)
	double optBoarder = 0;                      // 보더 크기
	bool optInvertPolarity = false;             // 이미지 극성 반전 여부
	bool optTestOnly = false;                   // 테스트 모드
	int optVerbose = 0;                         // 상세 출력 옵션
	unsigned rowsPerStrip = 512;                // TIFF 출력 시 스트립당 행 수
	bool optShowArea = false;                   // 이미지 면적 출력 옵션
	bool optQuiet = false;                      // 경고 및 메시지 숨기기 여부
	double total_area_cmsq = 0;                 // 이미지 면적 계산
	double optGrowSize = 0;                     // Grow 크기
	double optScaleX = 1;                       // X 축 스케일
	double optScaleY = 1;                       // Y 축 스케일
	unsigned int bytesPerScanline;              // 비트맵의 한 스캔라인 바이트 수
	unsigned int bitmapBytes;                   // 비트맵 전체 바이트 수
	unsigned char *bitmap;                      // 비트맵 데이터 포인터

//***********************************************************




//**********************************************************
// Optimised horizontal line drawing from x1,y to x2,y in the monochrome bitmap
// polarity specifies how pixels are changed.
// DRAW_ON = line is drawn bits set
// DRAW_OFF = line is drawn bits cleared
// DRAW_REVERSE  = line is drawn bits inverted
//
// global dependencies:	bytesPerScanline, bitmap
//**********************************************************

// 비트맵에서 특정 극성으로 가로선을 그리는 함수
void horizontalLine( int x1, int x2, unsigned char *buffer, Polarity_t polarity)
{
	if (x1 > x2)
		swap(x1, x2);
	// 범위 문제로 char -> unsigned char 변경
	static unsigned char fillSingle[64] = {
			0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0xC0, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0xE0, 0x60, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00,
			0xF0, 0x70, 0x30, 0x10, 0x00, 0x00, 0x00, 0x00,
			0xF8, 0x78, 0x38, 0x18, 0x08, 0x00, 0x00, 0x00,
			0xFC, 0x7C, 0x3C, 0x1C, 0x0C, 0x04, 0x00, 0x00,
			0xFE, 0x7E, 0x3E, 0x1E, 0x0E, 0x06, 0x02, 0x00,
			0xFF, 0x7F, 0x3F, 0x1F, 0x0F, 0x07, 0x03, 0x01 };

	static unsigned char fillLast[8]  = {0x80, 0xC0, 0xE0, 0xF0, 0xF8, 0xFC, 0xFE, 0xFF};
	static unsigned char fillFirst[8] = {0xFF, 0x7F, 0x3F, 0x1F, 0x0F, 0x07, 0x03, 0x01};


	const char b1 = (x1 & 7);
	const char b2 = (x2 & 7);

	unsigned char *px1 = buffer + (x1 >> 3);
	unsigned char *px2 = buffer + (x2 >> 3);

    // left pixel = MSB
    // right pixel = LSB
	switch (polarity)
	{
	case DARK:	// plot line with set bits
		// fill in the pixels at the byte x1, and x2 occupy.
		if (px1 == px2)
		{ // x1 and x2 occupy the same  byte
			*px1 |= fillSingle[ b1 + (b2<<3) ];
		}
		else
		{ // x1 and x2 occupy different bytes
			*px1 |= fillFirst[ b1 ];
			*px2 |= fillLast[ b2 ];
			// fill only the whole bytes in buffer between x1 and x2
			px1++;
			memset(px1, 0xFF, (px2 - px1));
		}
		break;

	case CLEAR:		// plot line with cleared bits

		if (px1 == px2)	// fill in the pixels at the byte x1, and x2 occupy.
		{ // x1 and x2 occupy the same  byte
			*px1 &= ~fillSingle[ b1 + (b2<<3) ];
		}
		else
		{ // x1 and x2 occupy different bytes
			*px1 &= ~fillFirst[ b1 ];
			*px2 &= ~fillLast[ b2 ];
			// fill only the whole bytes in buffer between x1 and x2
			px1++;
			memset(px1, 0x0, (px2 - px1));
		}
		break;

	case XOR: // invert the pixels
		// fill in the pixels at the byte x1, and x2 occupy.
		if (px1 == px2)
		{ // x1 and x2 occupy the same  byte
			*px1 ^= fillSingle[ b1 + (b2<<3) ];
		}
		else
		{ // x1 and x2 occupy different bytes
			*px1 ^= fillFirst[ b1 ];
			*px2 ^= fillLast[ b2 ];
			// XOR only the whole bytes in buffer between x1 and x2 (exclusive)
			px1++;
			while (px1 < px2)
			{
				*px1 ^= 0xFF;
				px1++;
			}
		}
		break;
	}

} // end HorizontalLine()




//---------------------------------------------------------------------------------
// 메인 함수: Gerber 파일 처리 및 TIFF 출력
int main (int argc, char **argv)
{
	clock_t  start_clock = clock();;
	string inputfile;
	string outputFilename;




	// create 256 element look up table for fast retrieve of
	// number of bits set in numbers 0 to 255.
	// used for calculating positive pixels in the drawn bitmap

	// LUT 초기화: 비트 수 계산
	for (int i=0; i < 256; i++)
	{
		nbitsTable[i]=0;
		if ((i&0x01)) nbitsTable[i]++;
		if ((i&0x02)) nbitsTable[i]++;
		if ((i&0x04)) nbitsTable[i]++;
		if ((i&0x08)) nbitsTable[i]++;
		if ((i&0x10)) nbitsTable[i]++;
		if ((i&0x20)) nbitsTable[i]++;
		if ((i&0x40)) nbitsTable[i]++;
		if ((i&0x80)) nbitsTable[i]++; // 활성 비트 수 계산
	}

	//
    // parse the command line
    // 명령줄 옵션 파싱
	while (1)
	{
        static struct option long_options[] =
          {
            // These options don't set a flag.
            // We distinguish them by their indices.
            {"dpi",     required_argument, 0, 'p'},
            {"output",  required_argument, 0, 'o'},
            {"negative",no_argument, 	   0, 'n'},
            {"area",    no_argument, 	   0, 'a'},
            {"test",    no_argument, 	   0,  't'},
            {"quiet",   no_argument, 	   0,  'q'},
            {"verbose", no_argument,   	   0,  'v'},
            {"scale-x", required_argument, 0, 1},
            {"scale-y", required_argument, 0, 2},
            {"help",    no_argument, 	   0,  3},
            {"grow-pixels",	required_argument, 0, 4},
            {"grow-mm",	required_argument, 0, 5},
            {"strip-rows",	required_argument, 0, 6},
            {"boarder-mm", required_argument, 0, 'b'},
            {"boarder-pixels", required_argument, 0, 7},
            {"rotation", required_argument, 0, 8},
            {0, 0, 0, 0}
          };
        // getopt_long stores the option index here.
        int option_index = 0;

        int c = getopt_long (argc, argv, "G:b:o:p:atvnq",
							long_options, &option_index);

		if (c == EOF)		break; // 모든 옵션 처리가 끝나면 루프 종료

		// 옵션별로 처리
		switch (c)
		{

		case 8: // 회전 옵션 처리
			optRotation = atof(optarg); // optarg 값을 double로 변환해 optRotation에 저장
		  break;
		case 7: // 보더 크기를 픽셀 단위로 설정
			optBoarder = atof(optarg); // optarg 값을 double로 변환해 optBoarder에 저장
			optBoarderUnitsMillimeters = false; // 보더 단위가 픽셀임을 명시
		  break;
		case 6: // TIFF 출력 시 스트립당 행 수 설정
			rowsPerStrip = atoi(optarg); // optarg 값을 정수로 변환하여 rowsPerStrip에 저장
		  break;
		case 5: // Grow 크기를 밀리미터 단위로 설정
		  optGrowSize = atof(optarg); // optarg 값을 double로 변환해 optGrowSize에 저장
		  optGrowUnitsMillimeters = true; // Grow 단위가 밀리미터임을 명시
		  break;
		case 4: // Grow 크기를 픽셀 단위로 설정
		  optGrowSize = atof(optarg); // optarg 값을 double로 변환해 optGrowSize에 저장
		  optGrowUnitsMillimeters = false; // Grow 단위가 픽셀임을 명시
		  break;
		case 3: // 도움말 메시지 출력
			fprintf( stdout,"%s", help_message); // stdout에 도움말 메시지 출력
			exit(0); // 프로그램 종료
		case 2: // Y 축 스케일 설정
		  optScaleY = atof(optarg); // optarg 값을 double로 변환해 optScaleY에 저장
		  break;
		case 1: // X 축 스케일 설정
		  optScaleX = atof(optarg); // optarg 값을 double로 변환해 optScaleX에 저장
		  break;
		case 'p': // DPI 설정
		  imageDPI = atof(optarg); // optarg 값을 double로 변환해 imageDPI에 저장
		  break; 
		case 'b': // 보더 크기를 밀리미터 단위로 설정
		  optBoarder = atof(optarg); // optarg 값을 double로 변환해 optBoarder에 저장
  		  optBoarderUnitsMillimeters = true; // 보더 단위가 밀리미터임을 명시
		  break; 
		case 'n': // 극성 반전 설정
		  optInvertPolarity = true; 
		  break; 
		case 't': // 테스트 모드 설정
		  optTestOnly = true; 
		  break;
		case 'a': // 이미지 면적 계산 및 출력 옵션
			optShowArea = true; 
		  break; 
		case 'v': // 상세 출력 모드
		  optVerbose++; // optVerbose 값을 증가
		  break;
		case 'q': // 경고 및 메시지 숨기기
		  optQuiet = true;
		  break;
		case 'o': // 출력 파일 이름 설정
			outputFilename = optarg; // optarg 값을 outputFilename에 저장
		  break; 
		case '?': // 잘못된 옵션 처리
		case ':': // 필수 인자가 없는 경우
		  fprintf (stderr, "Try 'gerb2tiff --help' for more information.\n"); // 오류 메시지 출력
		  return 1; // 프로그램 종료
		  break;
		}
	}

	// 상세 모드가 활성화된 경우 조용히 출력하는 옵션 해제
	if (optVerbose > 0 ) optQuiet = false;			// if user wants verbose, then cancel quiet option

	// DPI와 보더 값 검증
	if (imageDPI < 1)		error(string("DPI setting must be >= 1")); // DPI 값이 1보다 작으면 오류
	if (optBoarder < 0)		error(string("boarder setting must be >= 0")); // 보더 값이 0보다 작으면 오류

	// correct the units for some options
	// Grow 및 보더 단위 조정
	if ( optGrowUnitsMillimeters )
		optGrowSize *= imageDPI/25.4; // 밀리미터 단위를 픽셀로 변환
	if ( optBoarderUnitsMillimeters )
		optBoarder *= imageDPI/25.4; // 밀리미터 단위를 픽셀로 변환

	// Gerber 파일 리스트를 저장할 리스트 초기화
    list<Gerber *> gerbers;			// pointer to the list of Gerber object

	// 표준 입력으로부터 읽을지 여부 확인
    bool isStandardInput = false;
	if (optind == argc) // 인자가 없는 경우 표준 입력 사용
		isStandardInput = true;

	// 첫 번째 옵션 인덱스 저장
	int first_optind = optind;

	// Gerber 파일 처리 루프
	for(; optind < argc || isStandardInput; optind++)
	{
		FILE *file = 0; // 파일 포인터 초기화
		if ( isStandardInput ) // 표준 입력에서 파일 읽기
		{
			file = stdin;
			if (!optTestOnly && outputFilename.empty()) // 출력 파일 이름이 없는 경우 오류
			{
				cerr << "no output or input file specified.\n"
					    "Try 'gerb2tiff --help' for more information.\n";
				return 1;
			}
		}
		else // 명령줄 인자로부터 파일 읽기
		{
			inputfile = argv[optind]; // 현재 파일 이름 저장
			if ( outputFilename.empty())
					outputFilename = inputfile + ".tiff"; // 기본 출력 파일 이름 설정
			file = fopen( argv[optind], "rb"); // 파일 열기
			if (file == NULL)
					error( string("cannot open input file ")+inputfile ); // 파일 열기 실패 시 오류
			if (!optQuiet) // optQuiet 아닌 경우 파일 이름 출력
			{
				if (optind == first_optind)			cout << "gerb2tiff: ";
				if (!optQuiet && optind > first_optind)	cout << "+ ";
				cout << inputfile << " "<<flush;
			}
		}

		// Gerber 객체 생성 및 리스트에 추가
		gerbers.push_back( new Gerber(file, imageDPI, optGrowSize, optScaleX, optScaleY) );

		if (! isStandardInput)
			fclose(file);

		// print all warning messages
		for (int i=0; i < gerbers.back()->messages.size() && !optQuiet; i++)
		{
			if (i==0) std::cout <<"\n";
			std::cout <<"("<<inputfile<<") "<<gerbers.back()->messages[i]<<endl;	    		// print messages if any
		}
		// print error messages and abort
		if (gerbers.back()->isError)
		{
			std::cout <<"\n("<<inputfile<<") "<<gerbers.back()->errorMessage.str() << endl;
			return 1;		// exit program
		}
		if ( isStandardInput )
			break;

	}

	// 테스트 모드가 아니고 optQuiet 아닌 경우 출력 파일 이름 표시
	if (!optTestOnly  && !optQuiet)		cout << "-> "<<outputFilename;
	if (!optQuiet)						cout << endl;

	// Gerber 이미지의 최소/최대 좌표 초기화
	int miny =  INT_MAX;			// holds min and max dimentions of the occupied gerber images (superimposed)
	int minx =  INT_MAX;
	int maxy =  INT_MIN;
	int maxx =  INT_MIN;
    list<Polygon> globalPolygons;	// Contains polygons created by the all gerbers.

	// group all the polygons
	// 모든 Gerber 데이터를 병합해 다각형 리스트 생성
    for (list<Gerber*>::iterator it = gerbers.begin(); it != gerbers.end();  it++)
    {
       globalPolygons.merge((*it)->polygons ); // 각 Gerber 객체의 다각형 병합
}
	


//    for (int i=0; i < 100; i++)
//    {
//    	double radius = 50.0 * rand() / double(RAND_MAX);
//    	double x0  = 2000.0 * rand() / double(RAND_MAX);
//    	double y0  = 2000.0 * rand() / double(RAND_MAX);
//        globalPolygons.push_back(Polygon() );
//        globalPolygons.back().number = 1;
//        globalPolygons.back().vdata->add( 0,0);
//        globalPolygons.back().vdata->add(100,0);
//        globalPolygons.back().vdata->add(100,50);
//        globalPolygons.back().vdata->add( 0,50);
//        globalPolygons.back().vdata->rotate(222 *M_PI/180);
//        globalPolygons.back().vdata->initialise();
//        globalPolygons.back().initialise();
//    }

//    globalPolygons.sort();
//        globalPolygons.push_back(Polygon() );
//        globalPolygons.back().addArc(0, 2*M_PI, 10, 0, 0, false );
//        globalPolygons.back().number = 0;
//        globalPolygons.back().initialise();



	if (globalPolygons.size()==0 )// If nothing to draw then abort with error
		error("no image");

	

	// find extreme (x,y) coordinates for all polygons
	for (list<Polygon>::iterator it = globalPolygons.begin(); it != globalPolygons.end();  it++)
	{
		if (minx > it->pixelMinX) 	minx = it->pixelMinX;
		if (maxx < it->pixelMaxX) 	maxx = it->pixelMaxX;
		if (miny > it->pixelMinY) 	miny = it->pixelMinY;
		if (maxy < it->pixelMaxY)	maxy = it->pixelMaxY;
	}


	// use the world coordinate limits <maxx, minx, maxx, minx> to determine the
	// sized  of the bitmap buffer to allocate for drawing the image
	// always make image imageWidth multiple of 8
	// 보더 값을 포함하여 폭과 높이를 계산하고 항상 8의 배수로 맞춤

    unsigned imageWidth 	= unsigned(ceil ( (maxx - minx) + 2*optBoarder + 1 ));
    unsigned imageHeight	= unsigned(ceil ( (maxy - miny) + 2*optBoarder + 1 ));
	// 보더를 기준으로 x, y 오프셋 계산
    int xOffset		= int(floor( optBoarder ));
    int yOffset		= xOffset;

	// 이미지 극성을 결정 (1번째 Gerber 파일의 극성을 기준으로)
    bool isPolarityDark = true;
    isPolarityDark = (optInvertPolarity ^ gerbers.front()->imagePolarityDark);	// polarity is relative to 1st gerber file
    // 스트립의 높이가 이미지 높이보다 크거나 설정되지 않은 경우, 이미지 전체를 한 스트립으로 처리
	if ( rowsPerStrip > unsigned(imageHeight) || rowsPerStrip == 0)
    	rowsPerStrip = imageHeight;
	unsigned darkPixelsCount = 0;


    //
    // Eye candy
    //
	// 상세 모드에서 추가 정보 출력
    if (optVerbose >= 2)
    {
    	//printf("polygon count:               %d\n",globalPolygons.size()); //데이터 타입 불일치 오류
		std::cout << "polygon count:               " << globalPolygons.size() << std::endl;

    	printf ("grow option:                 %.1f pixels , %.3f mm\n", optGrowSize, optGrowSize/imageDPI*25.4);
    }
    if (optVerbose >= 1) // 이미지 정보 출력
    {
		printf ("Image data\n"
				"  origin (mm):               %.3f x %.3f\n"
				"  size (mm):                 %.3f x %.3f\n"
				"  size (pixels):             %u x %d\n"
				"  uncompressed size (MB):    %.1f\n"
				"  dots per inch:             %u\n"
				"  TIFF rows per strip        %u\n"
				,(-xOffset+minx)/imageDPI*25.4, (-yOffset+miny)/imageDPI*25.4
				,imageWidth/imageDPI*25.4, imageHeight/imageDPI*25.4
				,imageWidth, imageHeight
				,float( (((imageWidth+7) / 8) * imageHeight) / 0x100000)
				,int(imageDPI)
				,rowsPerStrip);

	}
    fflush(stdout); // 출력 버퍼를 비움

	if (optTestOnly)	// stop here on testing or if no Polygons to draw
	{
		if (optVerbose)
			printf("  time (sec):                %.2f\n",((double) (clock() - start_clock)) / CLOCKS_PER_SEC );
		return 0;
	}

	// Initialise TIFF with the libtiff library
	//
	TIFF* tif = TIFFOpen(outputFilename.c_str(), "w");
    if	(tif==NULL)
    {
    	cout << "error creating output file '" << outputFilename << "\n";;
    	return 1;
    }
	
	// TIFF 필드 설정
    TIFFSetField(tif, TIFFTAG_PLANARCONFIG, PLANARCONFIG_CONTIG);		// avoid errors, dispite TIFF spec saying this tag not needed in monochrome images.
    TIFFSetField(tif, TIFFTAG_PHOTOMETRIC, PHOTOMETRIC_MINISWHITE);		// white pixels are zero
    TIFFSetField(tif, TIFFTAG_COMPRESSION, COMPRESSION_CCITTRLE);		// use CCITT Group 3 1-Dimensional Modified Huffman run length encoding
    TIFFSetField(tif, TIFFTAG_IMAGELENGTH, imageHeight);
    TIFFSetField(tif, TIFFTAG_IMAGEWIDTH, imageWidth);
    TIFFSetField(tif, TIFFTAG_RESOLUTIONUNIT, 2);					// Resulution unit in inches
    TIFFSetField(tif, TIFFTAG_YRESOLUTION, imageDPI);
    TIFFSetField(tif, TIFFTAG_XRESOLUTION, imageDPI);
    TIFFSetField(tif, TIFFTAG_ROWSPERSTRIP, rowsPerStrip);

	//
    // Calculate size and allocate buffer for drawing. The image will be rendered sequential blocks of
    // imageWidth wide by rowsPerStrip high.
    //
	bytesPerScanline = ((imageWidth+7) >> 3);
	bitmapBytes = bytesPerScanline * rowsPerStrip;
    bitmap = (unsigned char *)malloc( bitmapBytes);
    if ( bitmap == 0 )
    	error("cannot allocate memory");


    //-----------------------------------------------------------------------
    // Draw polygons
    //-----------------------------------------------------------------------
    xOffset -= minx;


    int stripCounter = 0;
	list<Polygon>::iterator polyIterator = globalPolygons.begin();
    list<PolygonReference >  activePolys;

	// The bitmap will be divided into strips, of height rowsPerStrip.
	// Polygons are plotted for each strip consecutively in a loop, where the strip y coordinate equals ystart
    for (int ystart = miny - yOffset; ystart < ( int(imageHeight) + miny - yOffset); ystart += rowsPerStrip)
    {
    	// blank entire strip buffer, set pixels on/off depending on polarity of the 1st Gerber.
	    if (isPolarityDark)	memset(bitmap, 0x00, bitmapBytes);
	    else				memset(bitmap, 0xff, bitmapBytes);

	    unsigned char *bufferLine = bitmap;

	    // Loop over each row of the strip and fill with horizontal lines from the polygon raster data.
	    // All polygon are sorted in the list globalPolygons. Iterating each polygon for raster data will guarantee no missing lines.
		for (int y = ystart; (y-ystart) < rowsPerStrip && (y <= maxy); y++ , bufferLine += bytesPerScanline)
		{
			while (polyIterator != globalPolygons.end() && y == (polyIterator->pixelMinY))
			{
				activePolys.push_back( PolygonReference() );
				activePolys.back().polygon = &(*polyIterator);
				activePolys.sort();
//				printf("added poly %d (y=%d)\n", activePolys.back().polygon->number, y);
				polyIterator++;
			}

			for (list<PolygonReference>::iterator it = activePolys.begin();  it != activePolys.end();)
			{
				if (y > it->polygon->pixelMaxY)
				{
//					printf("erased poly %d (y=%d)\n", activePolys.back().polygon->number, y);
					it = activePolys.erase(it);
					continue;
				}
				int sliCount;
				int *sliTable;
				it->polygon->getNextLineX1X2Pairs( sliTable, sliCount);

//				printf("p %2d y:%d (x cnt %d) |",it->polygon->number, y, sliCount); fflush(stdout);

				Polarity_t pol =  it->polygon->polarity;
				if ((pol == DARK) && !isPolarityDark) pol = CLEAR;
				if ((pol == CLEAR) && isPolarityDark) pol = DARK;

				for (int i=0; i < sliCount; i+=2)
				{
//					printf(" %d~%d ",sliTable[i], sliTable[i+1] ); fflush(stdout);
					horizontalLine( xOffset + it->polygon->pixelOffsetX + sliTable[i], \
									xOffset + it->polygon->pixelOffsetX + sliTable[i+1], \
									bufferLine, pol  );

				}
//				printf("\n");
				it++;
			}
        }

		//
		// Write strip buffer to TIFF
		//
        unsigned lines = min (rowsPerStrip, imageHeight - rowsPerStrip * stripCounter);
        int percentComplete = (100*(stripCounter*rowsPerStrip + lines))/imageHeight;
	    if (optVerbose)
		{
	    	static int last = percentComplete;
	    	if (percentComplete != last )
	    		cout << "Rendering "<< percentComplete <<"%  \r"<<flush;
	    	last = percentComplete;
		}
    	TIFFWriteEncodedStrip(tif, stripCounter++, bitmap, bytesPerScanline*lines);

    	// Calculate positive area information
        if (optShowArea)
        {
			for (int i=0; i < lines; i++)
			{
				unsigned char *pbitmaprow = bitmap + bytesPerScanline * i;
				for (int x=0; x < bytesPerScanline; x++)
					darkPixelsCount += nbitsTable [ *pbitmaprow ];
					pbitmaprow++;
			}
        }

    }
    TIFFClose(tif);

    if (optVerbose)    	cout << "\n";

    if (optShowArea)
    {
    	printf("  dark  area (sq.cm):        %0.1f\n",darkPixelsCount*2.54*2.54/(imageDPI*imageDPI));
    	printf("  clear area (sq.cm):        %0.1f\n",((imageHeight*imageWidth) - darkPixelsCount*2.54*2.54)/(imageDPI*imageDPI));
    }

	if (optVerbose)
		printf("  time (sec):                %.2f\n",((double) (clock() - start_clock)) / CLOCKS_PER_SEC );

}




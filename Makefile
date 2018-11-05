all:
	g++ -g -std=c++11 -O3 -o smtsampler smtsampler.cpp -lz3

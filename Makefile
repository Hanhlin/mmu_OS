all: mmu.cpp
	g++ -gdwarf-3 -std=c++11 mmu.cpp -o mmu
clean:
	rm -f mmu *~
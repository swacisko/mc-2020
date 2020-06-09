//
// Created by sylwester on 5/21/20.
//

#include "combinatorics/GrayCode.h"

namespace GrayCode{

    /**
     *
     * @param n
     * @return gray code that is n-th in order.
     */
    int nthGrayCode( int n ){ return n ^ (n>>1); }

    /**
     *
     * @param g
     * @return reverse of given code - that is n such that nthGrayCode(n) == g
     */
    int nthGrayCodeReverse( int g ){
        int n = 0;
        for (; g; g >>= 1)
            n ^= g;
        return n;
    }

    /**
     *
     * @param n
     * @return index of the bit that is changed during transition between (n-1)-th gray code and n-th gray code, or -1 if n <= 0.
     */
    int getTransitionBit(int n){
        if( n <= 0 ) return -1;
        return __builtin_ctzll( nthGrayCode(n-1) ^ nthGrayCode(n) );
    }


    /**
     * For each subset of {0,1,..., 2^n-1} a function  fun(subset, d) is invoked, where subset is a subset encoded in binary and d is the index of the last changed element.
     * If a subset is empty, then d = -1, since no element was changed yet.
     * @param n
     * @param fun
     */
    void allSubsets( int n, function< void(int subset, int bit) > fun ){
        for( LL i=0; i < (1ll<<n); i++ ){
//            cerr << "transition bit for " << i << ": " << getTransitionBit(i) << endl;
            fun( nthGrayCode(i), getTransitionBit(i) );
        }
    }

    void test(){

        int N = 4;
        int x = 0;

        for( LL i=0; i < (1ll<<N); i++ ){
            cerr << "nthGrayCode(" << i << "): " << nthGrayCode(i) << endl;
            cerr << "binary of nthGrayCode(" << i << "):   ";  StandardUtils::writeInBinary( nthGrayCode(i), N );
            cerr << "Transition bit: " << getTransitionBit(i+1) << endl;

            ENDL(1);
        }

        allSubsets( N, [&x,&N](int subs, int a){
            cerr << "prev x: "; StandardUtils::writeInBinary(x,N);
            cerr << "subs  : "; StandardUtils::writeInBinary(subs,N);
            x ^= (1<<a);
            cerr << "curr x: "; StandardUtils::writeInBinary(x,N);
//            StandardUtils::writeInBinary(x,N);
            cerr << "bit changed: " << a << endl;

            ENDL(2);
        } );

        exit(1);
    }


}
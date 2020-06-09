//
// Created by sylwester on 10/1/19.
//

#ifndef ALGORITHMSPROJECT_GRAYCODE_H
#define ALGORITHMSPROJECT_GRAYCODE_H

#include "Makros.h"
#include "utils/StandardUtils.h"

/**
 * Gray code is a binary numeral system where two successive values differ in only one bit.
 * For example, the sequence of Gray codes for 3-bit numbers is: 000, 001, 011, 010, 110, 111, 101, 100, so G(4)=6.
 *
 * Let's look at the bits of number n and the bits of number G(n). Notice that i-th bit of G(n)
 * equals 1 only when i-th bit of n equals 1 and i+1-th bit equals 0 or the other way around (i-th bit equals 0 and i+1-th bit equals 1)
 */
namespace GrayCode{

    /**
     *
     * @param n
     * @return gray code that is n-th in order.
     */
    extern int nthGrayCode( int n );

    /**
     *
     * @param g
     * @return reverse of given code - that is n such that nthGrayCode(n) == g
     */
    extern int nthGrayCodeReverse( int g );
    /**
     *
     * @param n
     * @return index of the bit that is changed during transition between (n-1)-th gray code and n-th gray code, or -1 if n <= 0.
     */
    extern int getTransitionBit(int n);


    /**
     * For each subset of {0,1,..., 2^n-1} a function  fun(subset, d) is invoked, where subset is a subset encoded in binary and d is the index of the last changed element.
     * If a subset is empty, then d = -1, since no element was changed yet.
     * @param n
     * @param fun
     */
    extern void allSubsets( int n, function< void(int subset, int bit) > fun );

    extern void test();


}

#endif //ALGORITHMSPROJECT_GRAYCODE_H

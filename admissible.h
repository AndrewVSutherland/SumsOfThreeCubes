#ifndef _INCLUDE_ADMISSIBLE_
#define _INCLUDE_ADMISSIBLE_

#include <stdint.h>

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

// Computes admissible pairs (d,z) mod m determined by cubic reciprocity where
// m is the minimal divisor of 27k through which these constraints factor (m=27k if m is squarefree)
// ztab and zcnts are to be allocated by the caller, for d mod 27k coprime to 3
// sets zcnts[d] to number of admissible z and ztab[d] to an offset to returned array of shorts (allocated by admissible)
uint32_t admissible (uint16_t **zs, uint16_t *zmodulus, uint32_t *ztab, uint16_t *zcnts, uint16_t k);

#endif
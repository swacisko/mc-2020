//
// Created by sylwester on 5/22/20.
//

#ifndef ALGORITHMSPROJECT_TREEWIDTHDP_H
#define ALGORITHMSPROJECT_TREEWIDTHDP_H

#include "Makros.h"
#include "TreewidthDecomposition.h"

class TreewidthDP{
public:
    typedef int bitmask; // this MUST be either int or long long. No short, chars, unsigneds etc.

    TreewidthDP( VVI & V );
    TreewidthDP( NiceTreewidthDecomposition& decomp );
    virtual ~TreewidthDP();


    /**
     * This function should be implemented to process subset with given mask of an introduce-node num
     * Introduced node can ba accessed as decomp->introduces[num]
     * Son can be accessed as decomp->sons[num][0]
     * @param num
     * @param mask
     * @param mappedMask this is value of the subset mask in DP tables of sons of node num
     * @param bitChanged in case of processing mask using gray codes, this indicates the bit changed from last mask - used to update DP information
     */
    virtual void processIntroduceNodeMask( int num, bitmask mask, bitmask mappedMask, int bitChanged = -1 ) = 0;
    virtual void initIntroduceNode(int num) = 0; // does some stuff before calling @updateIntroduceNode(num)
    virtual void updateIntroduceNode(int num);

    /**
     * This function should be implemented to process subset with given mask of a forget-node num
     * Forgot node can ba accessed as decomp->forgets[num]
     * Son can be accessed as decomp->sons[num][0]
     * @param num
     * @param mask
     * @param mappedMask this is value of the subset mask in DP tables of sons of node num
     * @param bitChanged in case of processing mask using gray codes, this indicates the bit changed from last mask - used to update DP information
     */
    virtual void processForgetNodeMask( int num, bitmask mask, bitmask mappedMask, int bitChanged = -1 ) = 0;
    virtual void initForgetNode(int num) = 0; // does some stuff before calling @updateForgetNode(num)
    virtual void updateForgetNode(int num);

    /**
     * This function should be implemented to process subset with given mask of a join-node num
     * Sons can be accessed as decomp->sons[num][0] and decomp->sons[num][1]
     * @param num
     * @param mask
     * @param mappedMask this is value of the subset mask in DP tables of sons of node num
     * @param bitChanged in case of processing mask using gray codes, this indicates the bit changed from last mask - used to update DP information
     */
    virtual void processJoinNodeMask( int num, bitmask mask, bitmask mappedMask, int bitChanged = -1 ) = 0;
    virtual void initJoinNode(int num) = 0; // does some stuff before calling @updateJoinNode(num)
    virtual void updateJoinNode( int num );

    /**
     * Processes leaf nodes. Leaf nodes always have only 1 set (empty set)
     * @param num
     */
    virtual void processLeafNode(int num) = 0;

    /**
        * Runs dynamic programming on the decomposition.
        *
        * If decomp == nullptr then uses tw_iters iterations to find possibly best treewidth decomposition of the graph with flow_cutter
        * Otherwise it uses given decomposition @{decomp}
        * @param tw_iters
        */
    virtual void runDP(int tw_iters = 50);


    NiceTreewidthDecomposition*& getDecomposition(){ return decomp; }

    /**
     * Here should be implemented some function to access final result of DP programming
     */


    static void test();

    enum ENUMERATION_TYPE{
        ASC = 0, // enumeration from 0 to (1 << B) - 1. With remapping takes time O( B * 2^B ), but seem to be faster then O(2^B) due to constants
        DESC = 1, // enumeration from (1<<B - 1) to 0. With remapping takes time O( B * 2^B ), but seem to be faster then O(2^B) due to constants
        GRAY = 2, // enumeration using gray codes. Works in O(2^B), but there are a few operations more per each mask to generate gray codes
        BIT_ASC = 3, // enumeration of masks by number of set bits, ascending (first are numbers with 1 bit, then numbers with two set bits, three set bits, ...)
        BIT_DESC = 4 // enumeration of masks by number of set bits, descending (first are numbers with B set bits, then B-1, ...)
    };


    ENUMERATION_TYPE introduceEnumerationType = GRAY;
    ENUMERATION_TYPE forgetEnumerationType = GRAY;
    ENUMERATION_TYPE joinEnumerationType = GRAY;


protected:

    void enumerateSubsets( int num, ENUMERATION_TYPE type, function< void(int,bitmask,bitmask,int) > fun );

    /**
     * This function needs to be implemented to clear space of the dynamic programming tables.
     * It is invoked for sons of a node, after processing given node in dynamic programming.
     * Usually it will be something like vector<something>().swap( DP_TABLE[son] );
     */
    virtual void clearDPSpace(int son) = 0;

    /**
     * This function should initialize DP table for node num.
     * Typically it will be something like DP[num] = vector<something>( 1ll << bags[num].size() );
     * @param num
     */
    virtual void initializeDPTable(int num) = 0;

    /**
     * Initialize vectors of dp table. e.g DP = VVI(T)
     */
    virtual void initializeDPTable() = 0;

    VVI* V;
    int N; // size of V
    NiceTreewidthDecomposition *decomp = nullptr; // nice treewidth decomposition
    VVI tree; // tree structure of the nice treewidth decomposition
    int T; // size of the tree
    VVI bags; // bags of the decomposition

    unordered_map<int,int> ind2; // ind2[i] is the index of element i (from bags[num]) in bags[son]
    VI ind; // remapping - ind[i] is index such that element bags[num][i] == bags[son][ ind[i] ], or -1 if bags[num][i] is introduced node
    int forgetNodeIndex; // forgetNodeIndex is the index in ind2 of the forget node (remembered not to call ind2[v] in each iteration, since it is unneccessarily slow)

    /**
     * Here should be implemented some auxiliary DP structure, e.g. VVI DP;
     * It need not be initialized - it will be  automatically initialized within initializeDPTable() function in runDP()
     */

private:
    bool externalDecomposition = false;


};

#endif //ALGORITHMSPROJECT_TREEWIDTHDP_H

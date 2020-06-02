//
// Created by sylwester on 5/22/20.
//

#include <graphs/treewidth/TreewidthDP.h>
#include <graphs/treewidth/pace.h>
#include <combinatorics/GrayCode.h>

#include "graphs/treewidth/TreewidthDP.h"

TreewidthDP::TreewidthDP(VVI &V) {
    this->V = &V;
    N = V.size();

    cerr << "NOT TESTED YET!" << endl; exit(1);
}

TreewidthDP::TreewidthDP(NiceTreewidthDecomposition &decomp) {
    this->V = decomp.getV();
    tree = decomp.getStructure();
    T = tree.size();
    bags = decomp.getBags();

    this->decomp = &decomp;
//    this->decomp = new NiceTreewidthDecomposition(decomp);
    externalDecomposition = true;
}



TreewidthDP::~TreewidthDP() {
    if( decomp != nullptr && !externalDecomposition ){
        delete decomp;
        decomp = nullptr;
    }
}


void TreewidthDP::enumerateSubsets(int num, TreewidthDP::ENUMERATION_TYPE type, function<void(int, TreewidthDP::bitmask, TreewidthDP::bitmask, int)> fun) {
    int son = decomp->sons[num][0];


//    unordered_map<int,int> ind2;
    ind2.clear();
    VI sonBag = bags[son];
    for (int i = 0; i < sonBag.size(); i++) ind2[sonBag[i]] = i;


    int B = bags[num].size();
//    VI ind(B,-1); // remapping - ind[i] is index such that element bags[num][i] == bags[son][ ind[i] ]
    ind = VI(B, -1);
    for (int i = 0; i < B; i++) if (ind2.count(bags[num][i])) ind[i] = ind2[bags[num][i]];

    forgetNodeIndex = -1;
    if (decomp->forgets[num] != -1) forgetNodeIndex = ind2[decomp->forgets[num]];


    bitmask mappedMask = 0;

    switch( type ){
        case ASC:{
            for(bitmask i=0; i < ( 1ll << B ); i++){
                mappedMask = 0;
                for( bitmask j = 0; j < B; j++ ) if( ( i & (1ll << j) ) != 0 && ind[j] != -1 ) mappedMask |= ( 1ll << ind[j] );
                fun( num, i, mappedMask,-1 );
            }
            break;
        }
        case DESC:{
            for(bitmask i=(1ll<<B)-1; i >= 0; i--){
                mappedMask = 0;
                for( bitmask j = 0; j < B; j++ ) if( ( i & (1ll << j) ) != 0 && ind[j] != -1 ) mappedMask |= ( 1ll << ind[j] );
                fun( num, i, mappedMask,-1 );
            }
            break;
        }
        case GRAY:{
            mappedMask = 0;
            auto funGray = [=,&num, &mappedMask, &fun](long long mask, int bit){
                if( bit != -1 && /*bit != forgetNodeIndex && */ind[bit] != -1 ) mappedMask ^= ( 1ll << ind[bit] );
                fun(num, mask, mappedMask, bit);
            };
            GrayCode::allSubsets( B, funGray );
            break;
        }
        case BIT_ASC:{
            fun( num,0,0,-1 ); // mapped mask is the same as this mask - no need to remap. No nit changed
            for( int k=1; k<=B; k++ ){
                for(bitmask i=0; i < ( 1ll << B ); i++){
                    if( sizeof(bitmask) == 4 && __builtin_popcount(i) == k ){
                        for( bitmask j = 0; j < B; j++ ) if( ( i & (1ll << j) ) != 0 && ind[j] != -1 ) mappedMask |= ( 1ll << ind[j] );
                        fun( num, i, mappedMask,-1 );
                    }
                    else if( sizeof(bitmask) == 8 && __builtin_popcountll(i) == k ){
                        for( bitmask j = 0; j < B; j++ ) if( ( i & (1ll << j) ) != 0 && ind[j] != -1 ) mappedMask |= ( 1ll << ind[j] );
                        fun( num, i, mappedMask,-1 );
                    }
                }
            }
            break;
        }
        case BIT_DESC:{
            fun( num,0,0,-1 ); // mapped mask is the same as this mask - no need to remap. No nit changed
            for( int k=B; k>=1; k-- ){
                for(bitmask i=0; i < ( 1ll << B ); i++){
                    if( sizeof(bitmask) == 4 && __builtin_popcount(i) == k ){
                        for( bitmask j = 0; j < B; j++ ) if( ( i & (1ll << j) ) != 0 && ind[j] != -1 ) mappedMask |= ( 1ll << ind[j] );
                        fun( num, i, mappedMask,-1 );
                    }
                    else if( sizeof(bitmask) == 8 && __builtin_popcountll(i) == k ){
                        for( bitmask j = 0; j < B; j++ ) if( ( i & (1ll << j) ) != 0 && ind[j] != -1 ) mappedMask |= ( 1ll << ind[j] );
                        fun( num, i, mappedMask,-1 );
                    }
                }
            }
            break;
        }
        default:{
            cerr << "No default possible" << endl;
        }
    }
}



void TreewidthDP::updateIntroduceNode(int num) {
    initIntroduceNode(num);

    enumerateSubsets( num, introduceEnumerationType,
            [=]( int num, bitmask mask, bitmask mappedMask, int bitChanged ){
                processIntroduceNodeMask(num, mask, mappedMask,bitChanged);
            } );
}

void TreewidthDP::updateForgetNode(int num) {
    initForgetNode(num);
    enumerateSubsets( num, introduceEnumerationType,
                      [=]( int num, bitmask mask, bitmask mappedMask, int bitChanged ){
                          processForgetNodeMask(num, mask, mappedMask,bitChanged);
                      } );
}


void TreewidthDP::updateJoinNode(int num) {
    initJoinNode(num);
    enumerateSubsets( num, introduceEnumerationType,
                      [=]( int num, bitmask mask, bitmask mappedMask, int bitChanged ){
                          processJoinNodeMask(num, mask, mappedMask,bitChanged);
                      } );
}

void TreewidthDP::test() {

}

void TreewidthDP::runDP(int tw_iters) {

    if( decomp == nullptr ){
        TREEWIDTH trw;
        volatile sig_atomic_t tle = 0;
        TreewidthDecomposition dec = trw.main( *V, tw_iters, tle ); // just for test, better make it 100 for
        decomp = new NiceTreewidthDecomposition( *V, dec.getStructure(), dec.getBags() );
        tree = decomp->getStructure();
        T = tree.size();
        bags = decomp->getBags();
    }


    function< void(int num, int par) > dp = [=,&dp]( int num, int par ){

        for( int d : tree[num] ){
            if(d != par) dp(d,num);
        }

        initializeDPTable(num);

        if( decomp->introduces[num] != -1 ) updateIntroduceNode(num);
        else if( decomp->forgets[num] != -1 ) updateForgetNode(num);
        else if( decomp->sons[num].size() == 2 ) updateJoinNode(num);
        else processLeafNode(num);

        if( !decomp->sons[num].empty() ){
            for(int s : decomp->sons[num] ) clearDPSpace(s);
        }
    };

    initializeDPTable();

    int root = decomp->getRoot();
    dp( root, root );
}


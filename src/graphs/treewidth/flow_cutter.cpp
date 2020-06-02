//
// Created by sylwester on 4/24/20.
//

#include "graphs/treewidth/flow_cutter.h"

std::vector<flow_cutter::SourceTargetPair>  flow_cutter::select_random_source_target_pairs(int node_count, int cutter_count, int seed){
    std::vector<flow_cutter::SourceTargetPair>p(cutter_count);
    std::mt19937 rng(seed);
    for(auto&x:p){
        do{
            // We do not use std::uniform_distribution because it produces difference results for different compilers
            x.source = rng()%node_count;
            x.target = rng()%node_count;
        }while(x.source == x.target);
    }
    return p;
}
//
// Created by sylwester on 4/24/20.
//

#include "graphs/treewidth/node_flow_cutter.h"


flow_cutter::expanded_graph::Capacity capacity(int original_node_count, int original_arc_count){
    return {original_node_count, original_arc_count};
}
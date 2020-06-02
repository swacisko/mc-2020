//
// Created by sylwester on 8/8/19.
//


#include <graphs/GraphUtils.h>
#include <graphs/components/ConnectedComponents.h>

#include "graphs/GraphUtils.h"
#include <utils/StandardUtils.h>



VPII GraphUtils::getGraphEdges( VVI & V ){
    VPII res;
    res.reserve( countEdges(V) );
    for( int i=0; i<V.size(); i++ ){
        for( int d : V[i] ){
            if(d>i) res.push_back( {i,d} );
        }
    }
    return res;
}




int GraphUtils::countEdges(VVI &V) {
    int res = 0;
    for(auto& v : V) res += v.size();
    return res >> 1;
}



void GraphUtils::writeGraphHumanReadable(VVI &V) {
    cerr << "****" << endl;
    for( int i=0; i<V.size(); i++ ){
        cerr << i << ": ";
        VI neigh = V[i];
        sort(ALL(neigh));
        for(int d : neigh) cerr << d << "  ";
        cerr << endl;
    }
}
bool GraphUtils::isConnected(VVI &V) {
//    cerr << "isConnected not tested yet!" << endl; exit(1);
    VB was(V.size(),false);
    int cnt = 0;
    function< void(int) > dfs = [&V,&was, &dfs, &cnt](int num){
        was[num] = true;
        cnt++;
        for( int d : V[num] ) if( !was[d] ) dfs(d);
    };
    dfs(0);
    return (cnt == V.size());
}


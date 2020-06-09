//
// Created by sylwester on 5/19/20.
//

#include <graphs/treewidth/pace.h>
#include <graphs/GraphInducer.h>
#include <graphs/treewidth/TreewidthDecomposition.h>

#include "graphs/treewidth/TreewidthDecomposition.h"
#include "graphs/GraphUtils.h"

bool TreewidthDecomposition::isCorrect(){
    int N = V->size();
    int T = structure.size();
    VVI inBags(N);
    for( int i=0; i<T; i++ ){
        for( int b : bags[i] ) inBags[b].push_back(i);
    }

    { // checking if induced graphs are trees
        for( int i=0; i<N; i++ ){
            if( inBags.empty() ){
                cerr << "Node " << i << " is not contained in any bag" << endl;
                return false;
            }

            InducedGraph g = GraphInducer::induce(structure, inBags[i]);
//            if( Tree::isTree(g.V) == false ){
//                cerr << "graph induced by node that contain in bag vertex " << i << " is not a tree" << endl;
//                return false;
//            }
        }
    }

    { // checking if every edge is in some bag
        for( int i=0; i<N; i++ ) sort(ALL(inBags[i]));
        VPII edges = GraphUtils::getGraphEdges(*V);
        for(PII e : edges){
            int a = e.first;
            int b = e.second;
            VI inters;
            set_intersection( ALL(inBags[a]), ALL(inBags[b]), back_inserter(inters) );
            if( inters.empty() ){
                cerr << "edge " << e << " is not contained in any bag" << endl;
                return false;
            }
        }
    }

    return true;
}

int TreewidthDecomposition::getWidth() {
    if(width == -1){
        for(VI& b : bags) width = max(width,(int)b.size());
    }
    return width;
}


void NiceTreewidthDecomposition::makeItNice() {
    const bool debug = false;

    if(debug) cerr << "makeItNice()" << endl;

    VVI newTree; // new structure
    VVI newBags;
    int T = structure.size();
    int N = V->size();

    auto addEmptyEntry = [=,&newTree](){
        newTree.push_back(VI());
        this->par.push_back(-1);
        sons.push_back( VI() );
        introduces.push_back(-1);
        forgets.push_back(-1);
    };

    VB was(N, false);

    int depth = 0;
    function< void(int,int,int) > create = [=, &newTree, &newBags, &was, &N, &T, &debug, &create, &addEmptyEntry]( int num, int par, int depth ){
        if(debug){
            for( int i=0; i<depth; i++ ) cerr << "  "; cerr << "num = " << num << "    par = " << par << endl;
        }

        if( (structure[num].size() <= 1 && depth != 0) || structure.size() == 1 ){ // if in a leaf, not root, or the tree is just one node
            //*********  CREATING PATH OF INTRODUCE NODES
            if(debug){
                for( int i=0; i<depth; i++ ) cerr << "  ";
                cerr << "in a leaf!, creating introducing path" << endl;
            }
//            newTree.push_back(VI()); // adding a real leaf - node that represents abolutely nothing
            addEmptyEntry();
            newBags.push_back(VI()); // empty bag

            VI B;
            for( int b : bags[num] ){
                addEmptyEntry();

                int s = newTree.size();
                newTree[s-1].push_back(s-2);
                newTree[s-2].push_back(s-1);


                this->par[s-2] = s-1;
                sons[s-1].push_back(s-2);

                introduces[s-1] = b;
                B.push_back(b);

                newBags.push_back( B );

                if(debug){
                    for( int i=0; i<depth; i++ ) cerr << "  ";
                    cerr << "num = " << num << "   adding introduce node with bags: " << newBags.back() << endl;
                }
            }
        }

        for( int i=0; i<structure[num].size(); i++ ){ // the first element of structure[num] is its parent
            if( structure[num][i] == par ){
                swap( structure[num][i], structure[num][0] );
                break;
            }
        }

        VI toJoin;

        for( int d : structure[num] ){
            if( d != par ){
                create(d,num,depth+1);

                VI dBag = bags[d];
                VI numBag = bags[num];

                //********  CREATING PATH OF FORGET NODES
                for( int b : numBag ) was[b] = true;
                unordered_set<int> B( ALL(dBag) );
                for( int b : dBag ){
                    if( !was[b] ){
                        addEmptyEntry();

                        int s = newTree.size();
                        newTree[s-1].push_back(s-2);
                        newTree[s-2].push_back(s-1);
                        this->par[s-2] = s-1;
                        sons[s-1].push_back(s-2);

                        forgets[s-1] = b;
                        B.erase(b);

                        newBags.push_back( VI(ALL(B)) );

                        if(debug){
                            for( int i=0; i<depth; i++ ) cerr << "  ";
                            cerr << "num = " << num << "  d = " << d << "   adding forget node with bags: " << newBags.back() << endl;
                        }

                    }
                }
                for( int b : numBag ) was[b] = false;



                //*********  CREATING PATH OF INTRODUCE NODES
                for(int b : dBag) was[b] = true;
                for( int b : numBag ){
                    if( !was[b] ){
                        addEmptyEntry();

                        int s = newTree.size();
                        newTree[s-1].push_back(s-2);
                        newTree[s-2].push_back(s-1);
                        this->par[s-2] = s-1;
                        sons[s-1].push_back(s-2);

                        introduces[s-1] = b;
                        B.insert(b);

                        newBags.push_back( VI(ALL(B)) );

                        if(debug){
                            for( int i=0; i<depth; i++ ) cerr << "  ";
                            cerr << "num = " << num << "  d = " << d << "   adding introduce node with bags: " << newBags.back() << endl;
                        }

                    }
                }
                for(int b : dBag) was[b] = false;


                toJoin.push_back( (int)newTree.size()-1 );
            }
        }

        // now creating join nodes if possible
        if( !toJoin.empty() ) toJoin.pop_back(); // removing last node that is actually num node


        while( !toJoin.empty() ){
            int d = toJoin.back();
            toJoin.pop_back();

            addEmptyEntry();

            int s = newTree.size();
            newTree[s-1].push_back(d);
            newTree[d].push_back(s-1);
            this->par[d] = s-1;
            sons[s-1].push_back(d);

            newTree[s-1].push_back(s-2);
            newTree[s-2].push_back(s-1);
            this->par[s-2] = s-1;
            sons[s-1].push_back(s-2);

            newBags.push_back( newBags.back() );

            if(debug){
                for( int i=0; i<depth; i++ ) cerr << "  ";
                cerr << "num = " << num << "  d = " << d << "   adding JOIN node with bags: " << newBags.back() << endl;
            }
        }


        if(depth == 0){
            if(debug){
                for( int i=0; i<depth; i++ ) cerr << "  ";
                cerr << "in a root!, creating forget path" << endl;
            }

            VI B = bags[num];
            while( !B.empty() ){
                addEmptyEntry();

                int s = newTree.size();
                newTree[s-1].push_back(s-2);
                newTree[s-2].push_back(s-1);
                this->par[s-2] = s-1;
                sons[s-1].push_back(s-2);

                int b = B.back();
                B.pop_back();

                forgets[s-1] = b;

                newBags.push_back(B);

                if(debug){
                    for( int i=0; i<depth; i++ ) cerr << "  ";
                    cerr << "num = " << num << "   adding forget node with bags: " << newBags.back() << endl;
                }
            }

        }

    };

    if(debug) cerr << "Starting creation of nice decomposition" << endl;

    create(0,0,0);

    structure = newTree;
    bags = newBags;
    for( VI& b : bags ) sort(ALL(b)); // sorting all bags
    T = structure.size();
    root = T-1;
    par.resize(T);
    sons.resize(T);
    introduces.resize(T);
    forgets.resize(T);

}
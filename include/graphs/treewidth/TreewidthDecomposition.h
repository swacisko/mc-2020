//
// Created by sylwester on 4/16/20.
//

#ifndef ALGORITHMSPROJECT_TREEWIDTHDECOMPOSITION_H
#define ALGORITHMSPROJECT_TREEWIDTHDECOMPOSITION_H

//#include <graphs/GraphReader.h>
#include "Makros.h"

class TreewidthDecomposition{
public:

    TreewidthDecomposition(VVI& v, VVI str, VVI bg ) : V(&v), structure(str), bags(bg), width(-1) {}

    VVI& getStructure(){ return structure; }
    VVI& getBags(){ return bags; }
    VI& getBag(int p){ return bags[p]; }
    VVI* getV(){return V;}

    bool isCorrect();

    int getWidth();

protected:
    int width;

    VVI* V;
    VVI structure; // structure of the tree
    VVI bags; // bags[i] is the list of nodes that are contained in i-th tree node

};


class NiceTreewidthDecomposition : public TreewidthDecomposition{
public:

    NiceTreewidthDecomposition(VVI& v, VVI str, VVI bg ) : TreewidthDecomposition(v,str,bg) {
        makeItNice();
    }

    NiceTreewidthDecomposition( NiceTreewidthDecomposition& oth ) : TreewidthDecomposition( *oth.getV(), oth.getStructure(), oth.getBags() ) {
        root = oth.root;
        introduces = oth.introduces;
        forgets = oth.forgets;
        sons = oth.sons;
        par = oth.par;
    }


    int getRoot(){ return root; }

//private:
    int root;

    VI introduces; // introduces[i] is id of a node that is introduced when moving from sons[i][0] to i
    VI forgets; // forgets[i] is id of a node that is forgotten when moving from sons[i][0] to i
    VVI sons; // sons[i] are sons on vertex i. There are at most 2 sons. If there are 2, then i is a join node
    VI par; // parent of node i in the tree

    void makeItNice();

};


#endif //ALGORITHMSPROJECT_TREEWIDTHDECOMPOSITION_H

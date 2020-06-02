//
// Created by sylwester on 8/8/19.
//

#ifndef ALGORITHMSPROJECT_GRAPHUTILS_H
#define ALGORITHMSPROJECT_GRAPHUTILS_H

#include "Makros.h"

class GraphUtils {
public:


    static VPII getGraphEdges( VVI & V );

    /**
     *
     * @return number of edges of graph V
     */
    static int countEdges(VVI & V);


    static bool isConnected( VVI& V );

    static void writeGraphHumanReadable(VVI& V);

};


#endif //ALGORITHMSPROJECT_GRAPHUTILS_H

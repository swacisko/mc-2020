//
// Created by sylwester on 4/16/20.
//

#ifndef ALGORITHMSPROJECT_PACE_H
#define ALGORITHMSPROJECT_PACE_H




#include "graphs/treewidth/id_func.h"
#include "graphs/treewidth/list_graph.h"
#include "graphs/treewidth/multi_arc.h"
#include "graphs/treewidth/sort_arc.h"
#include "graphs/treewidth/chain.h"
#include "graphs/treewidth/flow_cutter.h"
#include "graphs/treewidth/greedy_order.h"

#include "graphs/treewidth/node_flow_cutter.h"
#include "graphs/treewidth/contraction_graph.h"
#include "graphs/treewidth/cch_order.h"
#include "graphs/treewidth/tree_decomposition.h"
#include "graphs/treewidth/separator.h"
#include "graphs/treewidth/TreewidthDecomposition.h"


#include <limits>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <sstream>
#ifdef PARALLELIZE
#include <omp.h>
#include <atomic>
#endif

#include <sys/time.h>
#include <unistd.h>

using namespace std;

struct TREEWIDTH {

    ArrayIDIDFunc tail, head;
    const char *volatile best_decomposition = 0;
    int best_bag_size = numeric_limits<int>::max();

    void ignore_return_value(int) {}

    int compute_max_bag_size(const ArrayIDIDFunc &order) {
        auto inv_order = inverse_permutation(order);
        int current_tail = -1;
        int current_tail_up_deg = 0;
        int max_up_deg = 0;
        compute_chordal_supergraph(
                chain(tail, inv_order), chain(head, inv_order),
                [&](int x, int y) {
                    if (current_tail != x) {
                        current_tail = x;
                        max_to(max_up_deg, current_tail_up_deg);
                        current_tail_up_deg = 0;
                    }
                    ++current_tail_up_deg;
                }
        );
        return max_up_deg + 1;
    }

    unsigned long long get_milli_time() {
        struct timeval tv;
        gettimeofday(&tv, NULL);
        return (unsigned long long) (tv.tv_sec) * 1000
               + (unsigned long long) (tv.tv_usec) / 1000;
    }

    const char *compute_decomposition(const ArrayIDIDFunc &order) {
        ostringstream out;
        print_tree_decompostion(out, tail, head, move(order));
        char *buf = new char[out.str().length() + 1];
        memcpy(buf, out.str().c_str(), out.str().length() + 1);
        return buf;
    }

    void test_new_order(ArrayIDIDFunc order) {
//        cerr << "testing new order" << endl;
        int x = compute_max_bag_size(order);

//        cerr << "max bag size computed, x = " << x << endl;

#ifdef PARALLELIZE
#pragma omp critical
#endif
        {
            if (x < best_bag_size) {
                best_bag_size = x;
                const char *old_decomposition = best_decomposition;

//                string s(old_decomposition);
//                DEBUG( s );

                best_decomposition = compute_decomposition(move(order));

//                string s = string(best_decomposition);
//                DEBUG(s);

                delete[]old_decomposition;
                {
                    string msg = "c status " + to_string(best_bag_size) + " " + to_string(get_milli_time()) + "\n";
//                    ignore_return_value(write(STDOUT_FILENO, msg.data(), msg.length()));
                }
            }
        }

//        cerr << "testing new order" << endl;
    }

//    char no_decomposition_message[] = "c info programm was aborted before any decomposition was computed\n";
    string no_decomposition_message = "c info programm was aborted before any decomposition was computed\n";

#ifdef PARALLELIZE
    volatile atomic_flag only_one_thread_in_signal_handler = ATOMIC_FLAG_INIT;
#endif

    void signal_handler(int) {
#ifdef PARALLELIZE
        while (only_one_thread_in_signal_handler.test_and_set()) {}
#endif

        const char *x = best_decomposition;
        if (x != 0)
            ignore_return_value(write(STDOUT_FILENO, x, strlen(x)));
        else
//            ignore_return_value(write(STDOUT_FILENO, no_decomposition_message, sizeof(no_decomposition_message))); // original
            ignore_return_value(write(STDOUT_FILENO, no_decomposition_message.c_str(), sizeof(no_decomposition_message.c_str())));

        _Exit(EXIT_SUCCESS);
    }

    /**
     *
     * @param V graph for which to construct decomposition
     * @param maxCnt - maximal number of times that a new order does not improve the solution
     * @param tle true if program received sigterm
     * @param argc
     * @return
     */
    TreewidthDecomposition main(VVI& V, int maxCnt, volatile sig_atomic_t& tle/*, int argc=1, char *argv[]*/) {
//        signal(SIGTERM, signal_handler);
//        signal(SIGINT, signal_handler);

//        signal(SIGSEGV, signal_handler);

//        swap(no_decomposition_message, "c info programm was aborted before any decomposition was computed\n");

        stringstream passToCin;

        int N = V.size();
        int E = 0; for(VI& v : V) E += v.size(); E >>= 1;
        passToCin << "p tw " << N << " " << E << endl;
        for( int i=0; i<N; i++ ) for( int d : V[i] ) if(d>i) passToCin << i+1 << " " << d+1 << endl;

        const char* cstr = passToCin.str().c_str();
//        cerr << "str(): " << passToCin.str() << endl;

        ignore_return_value( write( STDIN_FILENO, cstr, sizeof(cstr) ) );

        /*double startTime = clock();
        function<bool()> localLimitExceeded = [&startTime, &maxTimeMilis](){
            double now = clock();
            double milis = ( now - startTime ) / (double)CLOCKS_PER_SEC;
            milis *= 1000;

//            DEBUG(startTime);
//            DEBUG(now);
//            DEBUG(milis);
//            DEBUG(maxTimeMilis);
//
//            cerr << "returning: " << (milis > maxTimeMilis) << endl;
//            ENDL(1);

//            return (milis > maxTimeMilis);
            return true;
        };*/

        try {
            {
                string file_name = "-";
                auto g = uncached_load_pace_graph(file_name, passToCin);
                tail = std::move(g.tail);
                head = std::move(g.head);
            }

            int random_seed = 0;


//#ifdef PARALLELIZE
//#pragma omp parallel
//#endif
            {
                try {
//#ifdef PARALLELIZE
//#pragma omp sections nowait
//#endif
                    {

//                            test_new_order( compute_greedy_min_degree_order(tail, head) );
                        if(!tle  ){
//                            cerr << "testing compute_greedy_min_degree_order" << endl;
                            auto ord = compute_greedy_min_degree_order(tail, head);
                            if(!tle  ) test_new_order(ord);
//                            cerr << "\tfinished" << endl;
                        }
//#ifdef PARALLELIZE
//#pragma omp section
//#endif

//                        test_new_order(compute_greedy_min_shortcut_order(tail, head));

                        if(!tle ){
//                            cerr << "testing compute_greedy_min_shortcut_order" << endl;
                            auto ord = compute_greedy_min_shortcut_order(tail, head);
                            if(!tle ) test_new_order(ord);
//                            cerr << "\tfinished" << endl;
                        }
                    }

                    std::minstd_rand rand_gen;
                    rand_gen.seed(
                            random_seed
//#ifdef PARALLELIZE
//                            + omp_get_thread_num()
//#endif
                    );

                    flow_cutter::Config config;
                    config.cutter_count = 1;
                    config.random_seed = rand_gen();

                    bool improved = false;
                    int cnt = 0;
                    const int MAX_CNT = maxCnt;

                    auto extractTW = [ =,&V ](){
                        if( best_decomposition == 0 ) return (int)V.size();
                        istringstream res( best_decomposition );
                        int tw;
                        string empty;
                        res >> empty >> empty >> empty >> tw;
                        return tw;
                    };

                    int prevTW = extractTW();
//                    DEBUG(prevTW);

//                        cerr << endl;
                    for (int i = 0;; ++i) {
//                        cerr << "\rcnt: " << cnt << flush;



                        config.random_seed = rand_gen();
                        if (i % 32 == 0)
                            ++config.cutter_count;


//                        test_new_order( cch_order::compute_cch_graph_order(tail, head, flow_cutter::ComputeSeparator(config)) );

                        ArrayIDIDFunc ord;
                        if(!tle  ) ord = cch_order::compute_cch_graph_order(tail, head, flow_cutter::ComputeSeparator(config));
                        if(!tle ) test_new_order( ord );


                        int newTW = extractTW();

//                        DEBUG(prevTW);
//                        DEBUG(newTW);

                        if( newTW < prevTW ){
                            improved = true;
                            cnt=0;
                            prevTW = newTW;
                        }else{
                            improved = false;
                            cnt++;
                        }

                        if(tle || cnt > MAX_CNT ) break;

                    }

//                    string s(best_decomposition);
//                    DEBUG(s);


                    if( best_decomposition == 0 ) return TreewidthDecomposition( V, {}, {} ); // no treewidth decomposition, returning empty
                    istringstream res( best_decomposition );
                    string t;

                    int DECOMP_SIZE = -1, TW = -1, N = -1;
                    VVI BAGS;
                    VVI STRUCTURE;

                    while( getline(res,t) ){
//                        cerr << "t: " << t << endl;
                        if(t[0] == 'c') continue;

                        stringstream line(t);
                        string empty;
                        if( t[0] == 's' ){
                            line >> empty >> empty >> DECOMP_SIZE >> TW >> N;
                            BAGS = STRUCTURE = VVI( DECOMP_SIZE );

                        }else if( t[0] == 'b' ){
                            int a, id;
                            line >> empty >> id;
                            while( line >> a ) BAGS[id-1].push_back(a-1);
                        }else{
                            int a,b;
                            line >> a >> b;
                            STRUCTURE[a-1].push_back(b-1);
                            STRUCTURE[b-1].push_back(a-1);
                        }
                    }

//                    DEBUG(BAGS);

                    return TreewidthDecomposition(V, STRUCTURE, BAGS );
//

                } catch (...) {
                    cerr << "error1" << endl;
                    return TreewidthDecomposition( V, {}, {} );
                    signal_handler(0);
                }
            }
        } catch (...) {
            cerr << "error2" << endl;
            return TreewidthDecomposition( V, {}, {} );
            signal_handler(0);
        }
    }

};


#endif //ALGORITHMSPROJECT_PACE_H


#include <utils/TimeMeasurer.h>
#include "CONTESTS/MC20/mc20.h"



int main( int argc, char **argv  ) {
    TimeMeasurer::startMeasurement("main");

    ios_base::sync_with_stdio(0);
    cin.tie(NULL);


    MC20::run();

    TimeMeasurer::stopMeasurement("main");
    TimeMeasurer::writeAllMeasurements();

    return 0;
}
#include <vector>

extern std::vector<double> constraint_features;
extern std::vector<double> round_constraint_features;

extern std::vector<int> BBBowVec;
extern std::map<double, std::vector<float>> CurrBBEncodingMap;

extern void initBBBowVec();
extern void reset_BBBOW_Vec();
void reset_round_constraint_features();

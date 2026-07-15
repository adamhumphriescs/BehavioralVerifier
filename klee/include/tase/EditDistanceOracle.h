typedef std::map<std::string, std::vector<std::vector<uint64_t>>> msgToMedoidsMap ;
typedef std::map<std::string, msgToMedoidsMap> msgTypeMap;
void initializeEditDistanceOracle(std::string processedTrainingDataPath);
std::vector<std::string> getSimilarMessages(std::string msg, msgToMedoidsMap m, double alphaVal);
std::vector<std::vector<uint64_t>> getRandomFragSubset(std::vector<std::vector<uint64_t>> inputFrags, int betaVal);
double getMinEditDistancePrefixes(std::vector<uint64_t> path, std::vector<std::vector<uint64_t>> medoids);
std::vector<std::vector<uint64_t>> generatePhiN (std::string msgType, std::string msg, msgTypeMap fullMap);
extern std::vector<uint64_t> currMLBBWorkerFragment; //Worker uses this to track its basic blocks so far.  Resets
//when we hit a SEND or other fragment terminating instruction depending on the client.

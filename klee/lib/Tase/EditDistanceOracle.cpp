#include <vector>
#include <stdint.h>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <map>
#include <stack>
#include <vector>
#include <sstream>
#include <assert.h>
#include <limits.h>
#include <set>
#include "Cluster.h"
#include "EditDistance.h"

#include <algorithm>
#include <random>

#include <boost/unordered_map.hpp>

#include "tase_interp.h"

extern int taseDebug;
typedef std::map<std::vector<uint64_t>, std::vector<std::vector<uint8_t>>> medoidToMsgsMap;
typedef std::map<std::string, medoidToMsgsMap> msgType2MedoidToMsgsMap;
msgType2MedoidToMsgsMap clusteredTrainingData_medoid2Msgs;

typedef std::map<std::vector<uint8_t>, std::vector<std::vector<uint64_t>>> msgToMedoidsMap ;
typedef std::map<std::string, msgToMedoidsMap> msgType2MsgToMedoidsMap;
std::vector<std::vector<uint8_t>> getSimilarMessages(std::vector<uint8_t>, msgToMedoidsMap m, double alphaVal);
std::vector<std::vector<uint64_t>> getRandomFragSubset(std::vector<std::vector<uint64_t>> inputFrags, int betaVal);
std::map<std::string, msgToMedoidsMap> loadClusterMap( std::string fileName);
double getMinEditDistancePrefixes(std::vector<uint64_t> path, std::vector<std::vector<uint64_t>> medoids);
std::vector<std::vector<uint64_t>> generatePhiN (std::string msgType, std::vector<uint8_t> msg, msgType2MsgToMedoidsMap fullMap);
std::vector<uint64_t> currMLBBWorkerFragment; //Worker uses this to track its basic blocks so far.  Resets
//when we hit a SEND or other fragment terminating instruction depending on the client.

std::vector<uint8_t> getNextMsgBytes(std::ifstream & input);
std::vector<uint64_t> * fragVecFromString(std::string input);
int getMsgTypeNum(std::ifstream & input);
std::string getNextMsgType(std::ifstream & input);
int getNumEntries (std::ifstream & input);

std::vector<std::vector<uint8_t>> getNextMsgs(std::ifstream & input) {
  std::string line;
  getline(input, line);
  if (line.find("MSGS:") == std::string::npos) {
    printf("ERROR parsing cluster input file for MSG list; found string %s \n", line.c_str());fflush(stdout);
    std::exit(EXIT_FAILURE);
  }

  std::string msg = line.substr(line.find(":") +1);
  int numMsgs = atoi(msg.c_str());
  std::vector<std::vector<uint8_t>> msgs;
  for (int i = 0; i < numMsgs; i++) {
    std::vector<uint8_t> msg = getNextMsgBytes(input);
    msgs.push_back(msg);
  }
  return msgs;
}

std::vector<uint64_t> getNextFrag(std::ifstream & input) {
  std::string line;
  getline(input, line);
  std::vector<uint64_t> frag =  *(fragVecFromString(line));
  return frag;
}



std::map<std::string, medoidToMsgsMap> loadClustermap_medoid2Msgs(std::string fileName) {
  std::map<std::string, std::map<std::vector<uint64_t>, std::vector<std::vector<uint8_t>>> > res;


  std::ifstream input (fileName.c_str(), std::ifstream::in);
  if (input.peek() == std::ifstream::traits_type::eof()) {
    printf("ERROR: Didn't find cluster medoid2Msgs info in %s \n", fileName.c_str());fflush(stdout);
    exit(0);
  }

  //Look for
  //MSG TYPE NUM: X
  int num_msg_types = getMsgTypeNum(input);
  for (int i = 0; i < num_msg_types; i++) {
    std::string currMsgType = getNextMsgType(input); //Look for, e.g., MSG TYPE:864,SEND,
    std::map<std::vector<uint64_t>, std::vector<std::vector<uint8_t>>> currMap;
    int num_map_entries =  getNumEntries(input); //Loog for, e.g., NUM ENTRIES:32     
    for (int j = 0; j < num_map_entries; j++){
      std::vector<uint64_t> medoid = getNextFrag(input);
      std::vector<std::vector<uint8_t>> msgs = getNextMsgs(input);
      currMap.insert(std::make_pair(medoid, msgs));

    }
    res.insert(std::make_pair(currMsgType, currMap));
  }
  return res;  
}

void initializeEditDistanceOracle_medoid2Msgs(std::string processedTrainingDataPath ) {
  clusteredTrainingData_medoid2Msgs = loadClustermap_medoid2Msgs(processedTrainingDataPath);
  LOG_TASE("Entered medoid loading \n");LOG_FLUSH();
  for (msgType2MedoidToMsgsMap::iterator it = clusteredTrainingData_medoid2Msgs.begin(); it != clusteredTrainingData_medoid2Msgs.end(); ++it) {
    std::string msgType = it->first;
    medoidToMsgsMap m = it->second;
    LOG_TASE("Message type %s has %lu entries \n", msgType.c_str(), m.size());LOG_FLUSH();
    int i = 0;
    for (medoidToMsgsMap::iterator it2 = m.begin(); it2 != m.end(); ++it2) {
      LOG_TASE("-----------------\n");
      LOG_TASE("Medoid %d: \n", i);
      std::vector<uint64_t> currMed = it2->first;
      for (int j = 0; j < currMed.size(); j++) {
	LOG_TASE("%lu,", currMed[j]);
      }
      LOG_TASE("\n");

      std::vector<std::vector<uint8_t>> indicatorMsgs = it2->second;
      for (int j = 0; j < indicatorMsgs.size(); j++) {
	std::vector<uint8_t> currMsg = indicatorMsgs[j];
	LOG_TASE("Indicator Msg %d: ",j);LOG_FLUSH();
	for (int k = 0; k < currMsg.size(); k++) {
	  LOG_TASE("%x,", currMsg[k]);
	}
	LOG_TASE("\n");
      }
      i++;
    }
    
  }
  LOG_TASE("Leaving medoid loading \n");LOG_FLUSH();
}


//Call this before we start verification to make sure we can load the training data.
msgType2MsgToMedoidsMap clusteredTrainingData_msg2Medoids;
void initializeEditDistanceOracle(std::string processedTrainingDataPath) {
  clusteredTrainingData_msg2Medoids = loadClusterMap(processedTrainingDataPath);  

  for (msgType2MsgToMedoidsMap::iterator it = clusteredTrainingData_msg2Medoids.begin(); it != clusteredTrainingData_msg2Medoids.end(); ++it) {
    std::string msgType = it->first;
    msgToMedoidsMap m = it->second;

    printf("Message type %s has %lu entries \n", msgType.c_str(), m.size()); fflush(stdout);

  }
  printf("Finished loading cluster data from %s \n", processedTrainingDataPath.c_str());fflush(stdout);
  
}

//This is the most important method -- we would run this compute the priority for each "node" (worker )
// to implement the selection of a worker on line 105 of fig. 1 in Robby/Mike's 2013 paper.
extern double getWorkerPriorityEditDistance(std::vector<uint64_t> workerBasicBlockPath, std::string msgType, std::vector<uint8_t> msg) {
  //We really only need to compute PhiN once per message, so this is inefficiently recomputing it over and over
  std::vector<std::vector<uint64_t>> PhiN = generatePhiN(msgType, msg, clusteredTrainingData_msg2Medoids);
  //special case: No phiN can be generated, so return absurdly high edit distance.
  if (PhiN.size() == 0) {
    printf("IMPORTANT: Returning a high edit distance when no phiN can be generated \n");fflush(stdout);
    LOG_TASE("IMPORTANT: Returning a high edit distance when no phiN can be generated \n"); LOG_FLUSH();
    return 1000.0;
  }

  double priority = getMinEditDistancePrefixes(workerBasicBlockPath, PhiN);
  return priority;
}

double getWorkerPriorityEditDistanceWithPhiN (std::vector<uint64_t> workerBasicBlockPath, std::vector<std::vector<uint64_t>> PhiN) {
  //special case: No phiN can be generated, so return absurdly high edit distance.
  if (PhiN.size() == 0) {
    printf("IMPORTANT: Returning a high edit distance when no phiN can be generated \n");fflush(stdout);
    LOG_TASE("IMPORTANT: Returning a high edit distance when no phiN can be generated \n"); LOG_FLUSH();
    return 1000.0;
  }
  double priority = getMinEditDistancePrefixes(workerBasicBlockPath, PhiN);
  return priority;
}

/*
double getWorkerPriorityEditDistance(std::vector<uint64_t> workerBasicBlockPath, std::string msgType, std::string msg) {

  printf("ERROR Need to merge in updated tetrinet edit distance log \n");fflush(stdout);
  exit(0);
  
  //We really only need to compute PhiN once per message, so this is inefficiently recomputing it over and over
  std::vector<std::vector<uint64_t>> PhiN = generatePhiN(msgType, msg, clusteredTrainingData);
  //special case: No phiN can be generated, so return absurdly high edit distance.
  if (PhiN.size() == 0) {
    printf("IMPORTANT: Returning a high edit distance when no phiN can be generated \n");fflush(stdout);
    return 1000.0;
  }
  
  double priority = getMinEditDistancePrefixes(workerBasicBlockPath, PhiN);
  return priority;  
  
}
*/

typedef cliver::Score<std::vector<uint64_t>, uint64_t, int> BBScore;
typedef cliver::EditDistanceRow<BBScore,std::vector<uint64_t>,int> BBEDR;
double getFragmentEditDistanceNaive(std::vector<uint64_t> v1, std::vector<uint64_t> v2) {
  BBEDR bbedr(v1,v2);
  return (double) bbedr.compute_editdistance();
  
}


//Naively get edit distance between currPath and all possible prefixes of medoidPath; return the minimum of these.
//We should try to swap this with a better implementation that uses the Ukkonen optimizations or at least
//memoizes some of the previous results as supported by Cluster.h.  Some example code is in Clusterer.cpp.
double getMinEditDistancePrefixNaive(std::vector<uint64_t> currPath, std::vector<uint64_t> medoidPath ) {

  double bestDist = 10000000;//Make me DOUBLE_MAX or whatever the equivalent is.

  //Be careful with logic for prefixes because of use of .begin() below
  for (size_t i = 0; i < medoidPath.size() +1; i++) {
    std::vector<uint64_t> medoidPrefix (medoidPath.begin(), medoidPath.begin() + i); 
    double currDist = getFragmentEditDistanceNaive(currPath, medoidPrefix);
    if (currDist < bestDist) {
      bestDist = currDist;
    }
  }
  
  return bestDist;
}

double getMinEditDistancePrefixes(std::vector<uint64_t> path, std::vector<std::vector<uint64_t>> medoids) {
  double bestDist = 1000000; //Should make this DOUBLE_MAX or whatever the equivalent is

  for (size_t i = 0; i < medoids.size(); i++) {
    double currDist = getMinEditDistancePrefixNaive(path, medoids[i]);
    if (currDist < bestDist){
      bestDist = currDist;

    }
    
  }

  return bestDist;
}

typedef cliver::Score<std::string, char, int> StringScore;
typedef cliver::EditDistanceRow<StringScore,std::string,int> StringEDR;
double getStringEditDistance(std::string s1, std::string s2) {
  
  StringEDR edr(s1,s2);
  return (double) edr.compute_editdistance();
  
}


/*
typedef cliver::Score<std::vector<uint64_t>, uint64_t, int> BBScore;
typedef cliver::EditDistanceRow<BBScore,std::vector<uint64_t>,int> BBEDR;
double getFragmentEditDistanceNaive(std::vector<uint64_t> v1, std::vector<uint64_t> v2) {
  BBEDR bbedr(v1,v2);
  return (double) bbedr.compute_editdistance();

}
*/

typedef cliver::Score<std::vector<uint8_t>, uint8_t, int> ByteVecScore;
typedef cliver::EditDistanceRow<ByteVecScore,std::vector<uint8_t>,int> BVEDR;
double getByteVecEditDistance(std::vector<uint8_t> v1, std::vector<uint8_t> v2) {
  BVEDR bvedr(v1, v2);
  return (double) bvedr.compute_editdistance();
}

//Params from the "default" config in section 5.4 of the paper:
double alpha = 1.25;
int beta  = 8;
std::vector<std::vector<uint64_t>> generatePhiN_medoid2Msgs (std::string msgType, std::vector<uint8_t> msg, msgType2MedoidToMsgsMap mt2MedToMsgsMap, msgType2MsgToMedoidsMap mt2MsgToMedsMap) {
  LOG_TASE("Entering generatePhiN for medoid2msgs \n");
  medoidToMsgsMap medToMsgs = mt2MedToMsgsMap[msgType];
  msgToMedoidsMap msgToMedoids = mt2MsgToMedsMap[msgType];
  
  if (medToMsgs.size() == 0 || msgToMedoids.size() == 0) {
    printf("Warning: found no clusters starting with msgType %s\n", msgType.c_str());fflush(stdout);
    //Special case: return empty phiN
    std::vector<std::vector<uint64_t>> res;
    return res;
    //printf("ERROR finding map for msgType %s \n",msgType.c_str());fflush(stdout);
    //std::exit(EXIT_FAILURE);
  }
  LOG_TASE("Found %ld and %ld mappings for msgType %s\n",medToMsgs.size(), msgToMedoids.size(), msgType.c_str());

  std::vector<std::vector<uint8_t>> similarMessages  = getSimilarMessages(msg, msgToMedoids, alpha);
  LOG_TASE("generatePhiN_medoid2Msgs: found %lu similar messages \n", similarMessages.size());

  std::vector<std::vector<uint64_t>> candidateMedoids;
  //For each cluster, if any message in "similarMessages" is an indicator, make the cluster's medoid a candidate for phiN
  for (medoidToMsgsMap::iterator it = medToMsgs.begin(); it != medToMsgs.end(); ++it) {
    std::vector<uint64_t> currCluster = it->first;
    std::vector<std::vector<uint8_t>> indicatorMsgs = it->second;

    //For each message in similar messages, if the message is an indicator for currCluster, add it as a candidate
    //Why do we need to do a lookup from msg to medoids?
    bool messageIsIndicatorForCurrCluster = false;
    /*
    for (int i = 0; i < similarMessages.size(); i++) {
      auto it =  msgToMedoids.find(similarMessages[i]);
      if (it == msgToMedoids.end()) {
	LOG_TASE("ERROR: msgToMedoids lookup failed \n");
	exit(0);
      }
      std::vector<std::vector<uint64_t>> medoids = it->second;
      //bool messageIsIndicatorForCurrCluster = false;
      for (int i =0; i < medoids.size(); i++) {
	if (medoids[i] == currCluster) { //DANGER: Double check that this compares elements and  size
	  messageIsIndicatorForCurrCluster = true;
	}
      }
    }
    */
    for (int i = 0; i < similarMessages.size(); i++) {
      std::vector<uint8_t> currSimMessage = similarMessages[i];
      for (int j = 0; j < indicatorMsgs.size(); j++) {
	if (currSimMessage == indicatorMsgs[j]) {
	  messageIsIndicatorForCurrCluster = true;
	}
      }
      
    }
    if (messageIsIndicatorForCurrCluster) {
      candidateMedoids.push_back(currCluster);
    }
  }
  LOG_TASE("Candidate medoids size %lu \n", candidateMedoids.size());
  std::vector<std::vector<uint64_t>> res = getRandomFragSubset(candidateMedoids, beta);
  LOG_TASE("New phiN DBG size %d: \n", res.size());LOG_FLUSH();
  for (int i = 0; i < res.size(); i++) {
    std::vector<uint64_t> currRes = res[i];
    LOG_TASE("Random Frag %d \n", i);LOG_FLUSH();
    for (int j = 0; j < currRes.size(); j++) {
      LOG_TASE("%lld,", currRes[j]);LOG_FLUSH();
      
    }
    LOG_TASE("\n");
  }
  
  return res;
}
//Given a msgType indicating the type of fragment(e.g., "SEND,SEND," indicating a fragment that
//executes from a write syscall to another write syscall) and the msg itself we're trying to
//verify (e.g., "p 1 0 13 1"), produce the set of fragments phi_n (c.f., figure 1 in the 2013
//paper by robby and mike).

//For tetrinet there are only really two msg types based on how we've set up the modeled functions:
//"ENTRY,SEND," (which is trivial) and "SEND,SEND,".

std::vector<std::vector<uint64_t>> generatePhiN (std::string msgType, std::vector<uint8_t> msg, msgType2MsgToMedoidsMap fullMap) {
  LOG_TASE("Calling generatePhiN \n"); LOG_FLUSH();
  
  msgToMedoidsMap m = fullMap[msgType];
  if (m.size() == 0) {
    printf("Warning: found no clusters starting with msgType %s\n", msgType.c_str());fflush(stdout);
    //Special case: return empty phiN
    std::vector<std::vector<uint64_t>> res;
    return res;
    //printf("ERROR finding map for msgType %s \n",msgType.c_str());fflush(stdout);
    //std::exit(EXIT_FAILURE);
  }
  LOG_TASE("Found %ld mappings for msgType %s\n",m.size(), msgType.c_str());

  std::vector<std::vector<uint8_t>> similarMessages = getSimilarMessages(msg, m, alpha);
  LOG_TASE("Found %ld similar messages in getSimilarMessages \n", similarMessages.size());
  //if ( taseDebug > 1 ) {
    //LOG_TASE("Similar messages are \n");
    //for (size_t i = 0; i < similarMessages.size(); i++) {
      //LOG_TASE("%s\n", (char*)similarMessages[i].data()); //Not a string :(
    //}
  //}
  
  //Get all fragments associated with the set of similar messages
  std::vector<std::vector<uint64_t>> allSimilarFrags;
  for (size_t i = 0; i < similarMessages.size(); i++) {
    msgToMedoidsMap::iterator it = m.find(similarMessages[i]);
    if (it == m.end()) {
      printf("ERROR: could not find string in map in generatePhiN \n"); fflush(stdout);
      std::exit(EXIT_FAILURE);
    } else {
      std::vector<std::vector<uint64_t>> matchedFrags = it->second;
      for (int j = 0; j < matchedFrags.size(); j++) {
	allSimilarFrags.push_back(matchedFrags[j]);
      }      
    }
  }
  LOG_TASE("Found %lu frags close to message in generatePhiN \n", allSimilarFrags.size());
  printf("Found %lu frags close to message in generatePhiN \n", allSimilarFrags.size());fflush(stdout);

  LOG_TASE("Candidate medoids size %lu \n", allSimilarFrags.size());
  std::vector<std::vector<uint64_t>> res = getRandomFragSubset(allSimilarFrags, beta);

  //if ( taseDebug > 1 ) {

  LOG_TASE("Original phiN Debug size %d\n", res.size());LOG_FLUSH();
  for (int i = 0; i < res.size(); i++) {
      std::vector<uint64_t> currVec = res[i];
      
      LOG_TASE("Random fragment %d \n", i);
      for (int j = 0; j < currVec.size(); j++) {
	LOG_TASE("%ld \n", currVec[j]);
	

      }
      LOG_TASE("---------------\n");
    }
    //}
  return res;
  
}

std::vector<std::vector<uint64_t>> getRandomFragSubset(std::vector<std::vector<uint64_t>> inputFrags, int betaVal) {
  //In order to get a random subset of size betaVal, shuffle and just return the first betaVal values in the shuffled vector.

  //Easy case: only a few input frags.  No shuffling needed.

  if ( inputFrags.size() <= betaVal )
    return inputFrags;

  //Other case -- actually do the shuffle and return the first betaVal values.
  std::random_device devInput;
  auto randomness = std::default_random_engine{devInput()};

  std::vector<std::vector<uint64_t>> inputFragsCopy = inputFrags;
  std::shuffle(std::begin(inputFragsCopy),std::end( inputFragsCopy), randomness);
  
  std::vector<std::vector<uint64_t>> result;
  for (int i = 0; i < betaVal; i++) {
    result.push_back(inputFragsCopy[i]);
  }
  
  return result;

}

std::vector<std::vector<uint8_t>> getSimilarMessages(std::vector<uint8_t> msg , msgToMedoidsMap m, double alphaVal) {
  
  //Get all the keys in the msgToMedoidsMap
  std::vector<std::vector<uint8_t>> keys;
  for (msgToMedoidsMap::iterator it = m.begin(); it != m.end(); ++it) {
    keys.push_back(it->first);
  }
  printf("Found %ld keys\n", keys.size());fflush(stdout);
  
  //Find the closest message to msg
 //std::string bestMatch;
  std::vector<uint8_t> bestMatch;
  double bestDistance = 10000000;
  for (int i = 0; i < keys.size(); i++) {
    double currDistance = getByteVecEditDistance(msg, keys[i]);
    if (currDistance < bestDistance) {
      bestDistance = currDistance;
      bestMatch = keys[i];
    }
  }
  printf("bestDistance to msg is %lf \n", bestDistance);fflush(stdout);
 
  LOG_TASE("bestDistance to msg is %lf for frag: \n", bestDistance);LOG_FLUSH();
  for (int i = 0; i < bestMatch.size(); i++) {
    LOG_TASE("%d \n", bestMatch[i]);LOG_FLUSH();
  }
  
  //Return all msgs within alphaDist of closest message.
  double alphaDist = ((double) bestDistance) * alphaVal;
  std::vector<std::vector<uint8_t>> similarMsgs;
  for (int i = 0; i < keys.size(); i++) {
    double currDistance = getByteVecEditDistance(msg, keys[i]);
    if (currDistance <= alphaDist)
      similarMsgs.push_back(keys[i]);
    
  }
  printf("Returning %d similar msgs \n", similarMsgs.size()); fflush(stdout);
  LOG_TASE("Returning %d similar msgs \n", similarMsgs.size()); LOG_FLUSH();
  return similarMsgs;
  
}


std::string getNextMsgType(std::ifstream & input) {

  std::string line;
  getline(input, line);
  printf("Full msgtype string is:%s\n", line.c_str());fflush(stdout);
  if (line.find("MSG TYPE:") == std::string::npos) {
    printf("ERROR parsing cluster input file for msg type; found string %s \n", line.c_str());fflush(stdout);
    std::exit(EXIT_FAILURE);
  }

  std::string msgType = line.substr(line.find(":") +1);

  printf("Returning msg type:%s\n", msgType.c_str());fflush(stdout);
  return msgType;
  
}


std::vector<uint8_t> getNextMsgBytes(std::ifstream & input) {
  std::string line;
  getline(input, line);
  //If msg has commas, parse it with the assumption that each field is a byte
  char * msgCopy = strdup(line.c_str());
  char * tok = strtok(msgCopy, ",");
  std::vector<uint8_t> msgBytes;
  while (tok != NULL) {
    uint8_t currByte;
    //printf("Found tok %s \n", tok);fflush(stdout);
    sscanf(tok, "%hhx", &currByte);
    //printf("Scanned in as 0x%x \n", currByte);fflush(stdout);
    tok = strtok(NULL, ",");
    msgBytes.push_back(currByte);
  }
  return msgBytes;
  
}

std::string getNextMsg(std::ifstream & input) {
  std::string line;
  getline(input, line);
  if (line.find("MSG:") == std::string::npos) {
    printf("ERROR parsing cluster input file for msgTypeNum; found string %s \n", line.c_str());fflush(stdout);
    std::exit(EXIT_FAILURE);
  }

  std::string msg = line.substr(line.find(":") +1);

  printf("Returning msg :%s\n", msg.c_str());fflush(stdout);
  return msg;
  
}

std::vector<uint64_t> * fragVecFromString(std::string input) {

  std::vector<uint64_t> * res = new std::vector<uint64_t>;
  std::istringstream stream(input);
  std::string numStr;
  while( std::getline(stream,numStr, ',') ) {
    uint64_t val;
    std::istringstream conv(numStr);
    conv >> val;

    //printf("val is %lu \n", val);fflush(stdout);
    res->push_back(val);
  }
  printf("Length of fragment is %lu \n", res->size());fflush(stdout);
  return res;
}

int getMsgTypeNum(std::ifstream & input) {
  std::string line;
  getline(input, line);
  if (line.find("MSG TYPE NUM:") == std::string::npos) {
    printf("ERROR parsing cluster input file for msg type num list; found string %s \n", line.c_str());fflush(stdout);
    std::exit(EXIT_FAILURE);
  }

  std::string numStr = line.substr(line.find(":") +1);
  int num = atoi(numStr.c_str());
  return num;
}

int getNumEntries (std::ifstream & input) {
  std::string line;
  getline(input, line);
  if (line.find("NUM ENTRIES:") == std::string::npos) {
    printf("ERROR getting number of entries; found string %s \n", line.c_str());fflush(stdout);
    std::exit(EXIT_FAILURE);
  }
  printf("Full num entries string:%s\n", line.c_str());fflush(stdout);
  std::string numberString = line.substr(line.find(":") +1);
  int numEntries = atoi(numberString.c_str());
  return numEntries;
}

std::vector<std::vector<uint64_t>> getNextFragList(std::ifstream & input) {
  std::string line;
  getline(input, line);
  if (line.find("FRAGS:") == std::string::npos) {
    printf("ERROR parsing cluster input file for frag list; found string %s \n", line.c_str());fflush(stdout);
    std::exit(EXIT_FAILURE);
  }

  std::string msg = line.substr(line.find(":") +1);
  int numFrags = atoi(msg.c_str());

  std::vector<std::vector<uint64_t>> fragList;
  for (int i = 0; i < numFrags; i++) {
    getline(input, line);
    std::vector<uint64_t> frag =  *(fragVecFromString(line));
    fragList.push_back(frag);
  }

  return fragList;
}

std::map<std::string, msgToMedoidsMap> loadClusterMap( std::string fileName) {
  std::map<std::string,std::map<std::vector<uint8_t>, std::vector<std::vector<uint64_t>>>> res;

  std::ifstream input (fileName.c_str(), std::ifstream::in);
  if (input.peek() == std::ifstream::traits_type::eof()) {
    printf("ERROR: Didn't find cluster map info in %s \n", fileName.c_str());fflush(stdout);
    exit(0);
  }
  //Look for 
  //MSG TYPE NUM: X
  int num_msg_types = getMsgTypeNum(input);
  
  //int num_msg_types = 2; //Fix training to spit this out in the cluster file.  Hard coded for now.
  for (int i = 0; i < num_msg_types; i++) {
    std::string currMsgType = getNextMsgType(input);
    std::map<std::vector<uint8_t>,std::vector<std::vector<uint64_t>>> currMap;
    
    int num_map_entries = getNumEntries(input);
    for (int j = 0; j < num_map_entries; j++) {
      //std::string msg = getNextMsg(input);//
      std::vector<uint8_t> msg = getNextMsgBytes(input);
      
      std::vector<std::vector<uint64_t>> fragList = getNextFragList(input);
      currMap.insert(std::make_pair(msg,fragList));          
    }
    res.insert(std::make_pair(currMsgType, currMap));
    
    //Get rid of extra space between msg type mappings
    //std::string dummyLine;
    //std::getline(input, dummyLine);
    
  }
  return res;

  
}
/*
void testFunctions() {

  
  
  std::map<std::string, msgToMedoidsMap> bigMap = loadClusterMap("clusterMap");

  msgToMedoidsMap sendSendMap = bigMap["SEND,SEND,"];

  printf("%ld elements in sendSendMap \n", sendSendMap.size());

  std::vector<std::vector<uint64_t>> frags = sendSendMap["p 1 0 13 1"];
  printf("Found %ld elements in map \n",frags.size());

  generatePhiN("8552,SEND,", "p 1 0 13 1", bigMap);

  std::vector<uint64_t> samplePath = { 8552,8553,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9259,9260,9297,8552,8553,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9259,9260,9297,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9259,9260,9297,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9262,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9262,8552,8553,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9262,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9259,9260,9297,8552,8555,8559,8562,8564,8569,8574,8579,9248,9253,9254,9255,9257,9258,9259,9260,9297,8552,8555,8559,8562,8564,8569,8574,8579,9248,9342};

  initializeEditDistanceOracle("clusterMap");
  
  double priority  = getWorkerPriorityEditDistance(samplePath, "8552,SEND,", "p 1 1 15 3");
  printf("priority is %lf \n", priority);fflush(stdout);
  
  
}
*/

/*
int main() {

  testFunctions();
  
  
}
*/

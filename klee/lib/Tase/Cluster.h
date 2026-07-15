//===-- Cluster.h -----------------------------------------------*- C++ -*-===//
//
// <insert license>
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//
#ifndef CLIVER_CLUSTER_H
#define CLIVER_CLUSTER_H

#include <fstream>
#include <string>
#include <vector>
#include <list>
#include <limits.h>

namespace cliver {

////////////////////////////////////////////////////////////////////////////////

template <class Data> 
class DistanceMetric {
 public:
  virtual void init(std::vector<Data*> &datalist) = 0;
  virtual double distance(const Data* s1, const Data* s2) = 0;
};

////////////////////////////////////////////////////////////////////////////////

template <class Data, class Metric>
class GenericClusterer {
  typedef Data data_type;
  typedef Metric metric_type;

  // Add data to be clustered
  virtual void add_data(std::vector<Data*>& ) = 0;

  // Do the clustering
  virtual void cluster(size_t) = 0;

  // Print clusters
  virtual void print_clusters() = 0;

  // Number of clusters
  virtual size_t count() = 0;

  // Return all data elements assigned to this cluster id(including medoid)
  virtual void get_cluster(unsigned, std::vector<Data*> &) = 0;

  // Return data element assigned with cluster id
  virtual Data* get_medoid(unsigned) = 0;
};

template <class Data, class Metric>
class KMeansClusterer: public GenericClusterer<Data, Metric> {
 public:
  typedef Data data_type;
  typedef Metric metric_type;
  typedef std::pair<int, unsigned> id_dist_type;

  KMeansClusterer() {
    cost_ = INT_MAX;
    metric_ = new Metric();
  }
  ~KMeansClusterer() {}

  size_t count() { return count_; }

  void add_data(std::vector<Data*>& data) {
    data_.insert(data_.begin(), data.begin(), data.end());
    //std::cout << "added " << data.size() << " elements\n";
  }

  void cluster(size_t cluster_count = INT_MAX) {

    // Resize cluster if data size is too small
    if (data_.size() <= cluster_count) {
      count_ = data_.size();
      metric_->init(data_);
      clusters_.resize(data_.size(), 0);
      for (unsigned i=0; i < data_.size(); ++i) {
        set_medoid(medoids_.size(), i);
      }
      assign_all();
      return;
    } else {
      count_ = cluster_count;
    }

    // Initialize distance metric
    metric_->init(data_);

    // Select random first hub 
    srand(0);
    id_dist_type max = id_dist_type(0, rand() % data_.size());

    // Set all cluster to first random hub
    clusters_.resize(data_.size(), max.second);

    while (medoids_.size() < count_) {

      //std::cout << "Setting medoid " << medoids_.size()
      //    << " to data id " << max.second
      //    << ", dist is: " << max.first << "\n";

      set_medoid(medoids_.size(), max.second);
      max = id_dist_type(0, 0);

      #pragma omp parallel for schedule(dynamic)
      for (unsigned index=0; index < data_.size(); ++index) {
        //id_dist_type curr = find_closest_cluster(index, max.first);
        id_dist_type curr = find_cluster_less_than(index, max.first);

        clusters_[index] = curr.second;

        //std::cout << "Result: i=" << index 
        //    << ", dist=" << curr.first << ", medoid: " << is_medoid(index) << "\n";
        #pragma omp critical 
        if (!is_medoid(index) && curr.first >= max.first) {
          //std::cout << "New max, index=" << index << ", dist=" << curr.first << "\n";
          max.first = curr.first;
          max.second = index;
        }

      }
    }
    assign_all();
  }
   
  void print_clusters() {
    assign_all();
    for (unsigned id=0; id<medoids_.size(); ++id) {
      std::cout << "Medoid: " << *(data_[medoids_[id]]) << "\n";
      
      //std::cout << "Medoid: ";
      //for (unsigned j=0; j<(*(data_[medoids_[id]])).trace.size(); ++j) {
      //  std::cout << (*(data_[medoids_[id]])).trace[j] << " ";
      //}
      //std::cout << "\n";

      for (unsigned index=0; index<data_.size(); ++index) {
        if (clusters_[index] == id && !is_medoid(index)) {
          std::cout << "\t" << *(data_[index]) << "\n";
          //std::cout << "\t";
          //for (unsigned j=0; j<(*(data_[index])).trace.size(); ++j) {
          //  std::cout << (*(data_[index])).trace[j] << " ";
          //}
          //std::cout << "\n";
        }
      }
    }
  }

  // Adds all cluster members for given id to array, including medoid 
  void get_cluster(unsigned id, std::vector<Data*> &cluster_data) {
    for (unsigned index=0; index<data_.size(); ++index) {
      if (clusters_[index] == id) {
        cluster_data.push_back(data_[index]);
      }
    }
  }

  Data* get_medoid(unsigned id) {
    return data_[medoids_[id]];
  }

 private:

  void assign_all() {
    #pragma omp parallel for schedule(dynamic)
    for (unsigned i=0; i<data_.size(); ++i) {
      unsigned closest_cluster = find_closest_cluster(i).second;
      #pragma omp critical
      {
        clusters_[i] = closest_cluster;
      }
    }
  }

  std::pair<int, unsigned> find_closest_cluster(unsigned index) {

    if(is_medoid(index)) {
      for (unsigned id=0; id<medoids_.size(); ++id) {
        // This index is an medoid
        if (medoids_[id] == index)
          return std::make_pair(0,id);
      }
      assert(0);
    }

    double min_dist = metric_->distance(data_[index], data_[medoids_[0]]);
    unsigned min_id = 0;
    for (unsigned id=1; id<medoids_.size(); ++id) {
      // Compute distance
      double dist = metric_->distance(data_[index], data_[medoids_[id]]);

      // Update min distance medoid id
      if (dist < min_dist) {
        min_dist = dist;
        min_id = id;
      }
    }

    return std::make_pair(min_dist, min_id);
  }

  std::pair<int, unsigned> find_cluster_less_than(unsigned index, unsigned max) {

    if(is_medoid(index)) {
      for (unsigned id=0; id<medoids_.size(); ++id) {
        // This index is an medoid
        if (medoids_[id] == index)
          return std::make_pair(0,id);
      }
      assert(0);
    }

    double min_dist = metric_->distance(data_[index], data_[clusters_[index]]);
    unsigned min_id = clusters_[index];

    for (unsigned id=0; id<medoids_.size(); ++id) {

      if (min_dist < max)
        return std::make_pair(min_dist, min_id);

      // Skip first calculation
      if (medoids_[id] != clusters_[index]) {
        // Compute distance
        double dist = metric_->distance(data_[index], data_[medoids_[id]]);

        // Update min distance medoid id
        if (dist < min_dist) {
          min_dist = dist;
          min_id = id;
        }
      }
    }

    return std::make_pair(min_dist, min_id);
  }


  unsigned compute_configuration_cost() {
    unsigned cost = 0;
    for (unsigned index=0; index < data_.size(); ++index) {
      cost += find_closest_cluster(index).first;
    }
    return cost;
  }

  void assign_to_cluster(unsigned index) {
    clusters_[index] = find_closest_cluster(index).second;
  }

  void set_medoid(unsigned id, unsigned index) {
    
    assert(0 == medoid_set_.count(index));
    for (unsigned i=0; i<medoids_.size(); ++i) {
      assert(medoids_[i] != index);
    }

    // Assert this id is at most one more than size of medoids_
    assert(medoids_.size() <= id);

    if (medoids_.size() == id)
      medoids_.push_back(index);
    else
      medoids_[id] = index;

    medoid_set_.insert(index);
  }

  void replace_medoid(unsigned id, unsigned index) {
    assert(!is_medoid(index));
    assert(is_medoid(medoids_[id]));
    assert(1 == medoid_set_.count(medoids_[id]));
    assert(0 == medoid_set_.count(index));
    medoid_set_.erase(medoids_[id]);

    set_medoid(id, index);
  }

  bool is_medoid(unsigned index) {
    return medoid_set_.count(index) > 0;
  }

 private:
  unsigned count_;
  Metric* metric_;
  double cost_;

  std::vector<Data*> data_;        // map of data index to Data pointer
  std::vector<unsigned> clusters_; // map of data index to cluster id
  std::vector<int> medoids_;  // map of cluster id to data index
  std::set<unsigned> medoid_set_;  // set of data indicies that are medoids
};


template <class Data, class Metric>
class KMedoidsClusterer : public GenericClusterer<Data, Metric> {
 public:
  typedef Data data_type;
  typedef Metric metric_type;

  KMedoidsClusterer() {
    cost_ = INT_MAX;
    metric_ = new Metric();
  }
  ~KMedoidsClusterer() {}

  size_t count() { return count_; }

  void add_data(std::vector<Data*>& data) {
    data_.insert(data_.begin(), data.begin(), data.end());
    clusters_.resize(data_.size());
    //std::cout << "added " << data.size() << " elements\n";
  }

  void cluster(size_t cluster_count = INT_MAX) {

    // Resize cluster if data size is too small
    if (data_.size() < cluster_count)
      count_ = data_.size();
    else
      count_ = cluster_count;

    medoids_.resize(count_, -1);

    // Select random medoids
    //std::cout << "assigning random medoids...\n";
    for (unsigned i=0; i<count_; ++i) {
      unsigned r;
      srand(0);
      do {
        r = rand() % data_.size();
      } while (is_medoid(r));

      set_medoid(i, r);
    }

    // Initialize distance metric
    metric_->init(data_);

    bool cost_changed = false;

    while (true) {
      //std::cout << "while loop begins...\n";
      printf("Cost is %lf \n", cost_);fflush(stdout);
      for (unsigned id=0; id < count_; ++id) {
        //std::cout << "id = " << id << "\n";

        for (unsigned index=0; index < data_.size(); ++index) {
          //std::cout << "index = " << index << "\n";
          if (!is_medoid(index)) {
            unsigned prev_index = medoids_[id];
            replace_medoid(id, index);
            unsigned cost = compute_configuration_cost();

            if (cost < cost_) {
              cost_changed = true;
              cost_ = cost;
              break;
            } else {
              replace_medoid(id, prev_index);
            }
          }
        }
      }

      if (!cost_changed)
        break;
      else
        cost_changed = false;
    }

    // Assign all data to closest medoid
    assign_all();
  }
   
  void print_clusters() {
    assign_all();
    for (unsigned id=0; id<medoids_.size(); ++id) {
      //std::cout << "Medoid: " << *(data_[medoids_[id]]) << "\n";
      
      //std::cout << "Medoid: ";
      //for (unsigned j=0; j<(*(data_[medoids_[id]])).trace.size(); ++j) {
      //  std::cout << (*(data_[medoids_[id]])).trace[j] << " ";
      //}
      //std::cout << "\n";

      for (unsigned index=0; index<data_.size(); ++index) {
        if (clusters_[index] == id && !is_medoid(index)) {
          //std::cout << "\t" << *(data_[index]) << "\n";
          //std::cout << "\t";
          //for (unsigned j=0; j<(*(data_[index])).trace.size(); ++j) {
          //  std::cout << (*(data_[index])).trace[j] << " ";
          //}
          //std::cout << "\n";
        }
      }
    }
  }

  // Adds all cluster members for given id to array, including medoid 
  void get_cluster(unsigned id, std::vector<Data*> &cluster_data) {
    for (unsigned index=0; index<data_.size(); ++index) {
      if (clusters_[index] == id) {
        cluster_data.push_back(data_[index]);
      }
    }
  }

  Data* get_medoid(unsigned id) {
    return data_[medoids_[id]];
  }

 private:

  void assign_all() {
    for (unsigned i=0; i<data_.size(); ++i)
      assign_to_cluster(i);
  }

  std::pair<int, unsigned> find_closest_cluster(unsigned index) {

    if(is_medoid(index)) {
      for (unsigned id=0; id<medoids_.size(); ++id) {
        // This index is an medoid
        if (medoids_[id] == index)
          return std::make_pair(0,id);
      }
      assert(0);
    }

    double min_dist = metric_->distance(data_[index], data_[medoids_[0]]);
    unsigned min_id = 0;
    for (unsigned id=1; id<medoids_.size(); ++id) {
      // Compute distance
      double dist = metric_->distance(data_[index], data_[medoids_[id]]);

      // Update min distance medoid id
      if (dist < min_dist) {
        min_dist = dist;
        min_id = id;
      }
    }

    return std::make_pair(min_dist, min_id);
  }

  unsigned compute_configuration_cost() {
    unsigned cost = 0;
    for (unsigned index=0; index < data_.size(); ++index) {
      cost += find_closest_cluster(index).first;
    }
    return cost;
  }

  void assign_to_cluster(unsigned index) {
    clusters_[index] = find_closest_cluster(index).second;
  }

  void set_medoid(unsigned id, unsigned index) {
    
    assert(0 == medoid_set_.count(index));
    for (unsigned i=0; i<medoids_.size(); ++i) {
      assert(medoids_[i] != index);
    }

    medoids_[id] = index;
    medoid_set_.insert(index);
  }

  void replace_medoid(unsigned id, unsigned index) {
    assert(!is_medoid(index));
    assert(is_medoid(medoids_[id]));
    assert(1 == medoid_set_.count(medoids_[id]));
    assert(0 == medoid_set_.count(index));
    medoid_set_.erase(medoids_[id]);

    set_medoid(id, index);
  }

  bool is_medoid(unsigned index) {
    return medoid_set_.count(index) > 0;
  }

 private:
  unsigned count_;
  Metric* metric_;
  double cost_;

  std::vector<Data*> data_;        // map of data index to Data pointer
  std::vector<unsigned> clusters_; // map of data index to cluster id
  std::vector<int> medoids_;  // map of cluster id to data index
  std::set<unsigned> medoid_set_;  // set of data indicies that are medoids
};

////////////////////////////////////////////////////////////////////////////////

} // end namespace cliver

#endif // CLIVER_CLUSTERER_H


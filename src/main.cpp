#include "art_set.h"
#include "art_map.h"

#include "art.h"
#include <fstream>
#include <iostream>
#include <string_view>
#include <vector>
using namespace std;

struct DataSet {
    std::vector<string> data;
    DataSet() {
        auto dname = std::string("/data/hashtable-testdata/Hotspot.tsv");
        std::ifstream ifs(dname);
        for (std::string s; std::getline(ifs, s);)
            data.push_back(std::move(s));
    }
};

int main(int argc, char* argv[]) {
    std::cout << alignof(art_set_ns::art_leaf) << std::endl;
    DataSet ds;
    // art_tree s;
    // art_tree_init(&s);
    // int flag = 1;
    // for (auto& c : ds.data) {
    //     art_insert(&s, (const unsigned char*)c.data(), c.size(), &flag);
    // }

    // for (auto& c : ds.data) {
    //     if (!art_search(&s, (const unsigned char*)c.data(), c.size()))
    //         std::cout << c << std::endl;
    // }

    art_set a;
    for (auto& c : ds.data) {
        a.emplace(c.data(), c.size());
    }

    for (auto& c : ds.data) {
        if (!a.find(c.data(), c.size()))
            std::cout << c << std::endl;
    }
    std::cout << a.size() << std::endl;
    // a.emplace(s[1].data(), s[1].size(), 2);
    // a.emplace(s[2].data(), s[2].size(), 3);

    // std::cout << *a.find(s[0].data(), s[0].size()) << std::endl;
    // std::cout << *a.find(s[1].data(), s[1].size()) << std::endl;
    // std::cout << *a.find(s[2].data(), s[2].size()) << std::endl;
    return 0;
}

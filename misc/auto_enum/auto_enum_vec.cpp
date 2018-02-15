#include <iostream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

template<typename IntType>
class AutoEnumVec
{
    std::vector<IntType> vec_;
    std::unordered_map<std::string, IntType> map_;
    IntType next_{0};

public:
    void push_back(const std::string& s)
    {
        auto p = map_.insert(std::make_pair(s, next_));
        vec_.push_back(p.first->second);
        if (p.second)
            next_++;
    }

    const std::vector<IntType>& get_vec() const
    {
        return vec_;
    }

    const std::unordered_map<std::string, IntType>& get_map() const
    {
        return map_;
    }
};

int main()
{
    AutoEnumVec<unsigned> aev;
    aev.push_back("AAA");
    aev.push_back("AAB");
    aev.push_back("AAA");
    aev.push_back("AAA");
    std::cout << "vec: ";
    for (auto e : aev.get_vec())
        std::cout << e << " ";
    std::cout << "\n";
    std::cout << "map: ";
    for (auto p : aev.get_map())
        std::cout << "(\"" << p.first << "\", " << p.second << ") ";
    std::cout << "\n";
}

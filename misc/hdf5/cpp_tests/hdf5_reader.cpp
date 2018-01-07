#include <H5Cpp.h>
#include <cstdio>

herr_t print_datasets(hid_t, const char *member_name, void *h5Fp)
{
    printf("%s\n", member_name);
    H5::DataSet ds = ((H5::H5File*)h5Fp)->openDataSet(member_name);
    H5::StrType read_type(0, H5T_VARIABLE);
    H5::DataSpace dspace(H5S_SCALAR);
    std::string field_value;
    ds.read(field_value, read_type, dspace);
    printf("Contents: ");
    printf("%s\n", field_value.c_str());
    return 0;
}

std::string readStrScalarDS(H5::H5File& h5Fp, const std::string& dsName)
{
    auto ds = h5Fp.openDataSet(dsName);
    H5::StrType readType(0, H5T_VARIABLE);
    H5::DataSpace dSpace(H5S_SCALAR);
    std::string ret;
    ds.read(ret, readType, dSpace);
    return ret;
}

int main(int argc, char *argv[])
{
    if (argc != 2)
        return 1;
    std::string dsName = argv[1];
    H5::H5File h5Fp("many_jsons.h5", H5F_ACC_RDONLY);
    printf("Reading contents of '%s'...\n", dsName.c_str());
    auto contents = readStrScalarDS(h5Fp, dsName);
    printf("%s\n", contents.c_str());
    //int idx = 0;
    //h5Fp.iterateElems("/", &idx, print_datasets, (void *)&h5Fp); 
    return 0;
}

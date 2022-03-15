#include <cstdlib>

extern "C" int32_t** parseArrays(int32_t argc, const char* argv[], int32_t& arrlength) {
    if (argc <= 2) return nullptr;

    arrlength = std::atoi(argv[1]);
    if (arrlength * 2 + 2 != argc) return nullptr;

    int32_t* ptr     = reinterpret_cast<int32_t*>(std::malloc(2 * arrlength * sizeof(int32_t)));
    int32_t** ptrPtr = reinterpret_cast<int32_t**>(std::malloc(2 * sizeof(int32_t*)));
    ptrPtr[0]        = ptr;
    ptrPtr[1]        = ptr + arrlength;
    for (int i = 0; i < arrlength; ++i) {
        ptr[i]             = std::atoi(argv[i]);
        ptr[arrlength + i] = std::atoi(argv[arrlength + i]);
    }
    return ptrPtr;
}

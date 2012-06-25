#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <set>
#include <sstream>
#include <vector>

#include <boost/program_options.hpp>
#include <boost/array.hpp>

#include "anydsl/literal.h"
#include "anydsl/lambda.h"
#include "anydsl/dump.h"
#include "anydsl/primop.h"
#include "anydsl/world.h"
#include "impala/parser.h"
#include "impala/ast.h"
#include "impala/sema.h"
#include "impala/dump.h"
#include "impala/emit.h"
#include "impala/type.h"
#include "impala/init.h"

//------------------------------------------------------------------------------

using namespace anydsl;
using namespace std;
namespace po = boost::program_options;

typedef vector<string> Names;

//------------------------------------------------------------------------------

enum EmitType {
    None,
    AIR,
    LLVM,
};

int main(int argc, char** argv) {
    try {
        if (argc < 1)
            throw logic_error("bad number of arguments");

        string prgname = argv[0];
        Names infiles;
        string outfile = "-";
        string emittype;
        EmitType destinationType = None;
        bool help, fancy, run, notc, debug, tracing = false;

        // specify options
        po::options_description desc("Usage: " + prgname + " [options] file...");
        desc.add_options()
        ("help,h",      po::bool_switch(&help), "produce this help message")
        ("emit,e",      po::value<string>(&emittype),   "emit code, arg={air|llvm}")
        ("fancy,f",     po::bool_switch(&fancy), "use fancy air output")
        ("run,r",       po::bool_switch(&run),  "run program")
        ("notc",        po::bool_switch(&notc),  "no typechecks during execution")
        ("debug,d",     po::bool_switch(&debug), "print debug information during execution")
        ("trace,t",     po::bool_switch(&tracing), "print tracing information during execution")
        ("outfile,o",   po::value(&outfile)->default_value("-"), "specifies output file")
        ("infile,i",    po::value(&infiles),    "input file");

        // positional options, i.e., input files
        po::positional_options_description pos_desc;
        pos_desc.add("infile", -1);

        // do cmdline parsing
        po::command_line_parser clp(argc, argv);
        clp.options(desc);
        clp.positional(pos_desc);
        po::variables_map vm;

        po::store(clp.run(), vm);
        po::notify(vm);

        if (!emittype.empty()) {
            if (emittype == "air")
                destinationType = AIR;
            else if (emittype == "llvm")
                ANYDSL_NOT_IMPLEMENTED;
            else
                throw logic_error("invalid emit type: " + emittype);
        }

        if (infiles.empty() && !help)
            throw po::invalid_syntax("infile", po::invalid_syntax::missing_parameter);

        if (help) {
            desc.print(cout);
            return EXIT_SUCCESS;
        }

        ofstream ofs;
        if (outfile != "-") {
            ofs.open(outfile.c_str());
            ofs.exceptions(istream::badbit);
        }
        //ostream& out = ofs.is_open() ? ofs : cout;


        if (debug) { 
            ANYDSL_NOT_IMPLEMENTED;
        }

        const char* filename = infiles[0].c_str();
        ifstream file(filename);
        impala::init();
        impala::TypeTable types;
        anydsl::AutoPtr<const impala::Prg> p(impala::parse(types, file, filename));
        dump(p, true);
        check(types, p);
        World w;
        Lambda* l = new Lambda();
        Param* pa = l->appendParam(w.type_u32());
        Param* pb = l->appendParam(w.type_u32());
        pa->debug = "a";
        pb->debug = "b";
        l->calcType(w);
        const Def* args[] = { w.literal_u32(42), w.literal_u32(23) };
        const Jump* jump = w.createJump(l, args);
        l->setJump(jump);
        const Lambda* newl = w.finalize(l);
        dump(newl);

        std::cout << std::endl;
        const Value* add = w.createArithOp(ArithOp_add,  pa, w.literal_u32(42));
        const Value* mul = w.createArithOp(ArithOp_mul, add, w.literal_u32(23));
        mul->dump();
        std::cout << std::endl;


        emit(w, p);
        impala::destroy();
        
        //Emit the results
        switch (destinationType) {
            case None:
                break;
            case AIR:
                ANYDSL_NOT_IMPLEMENTED;
                break;
            case LLVM:
                ANYDSL_NOT_IMPLEMENTED;
                break;
        }
        return EXIT_SUCCESS;
    } catch (exception const& e) {
        cerr << e.what() << endl;
        return EXIT_FAILURE;
    } catch (...) {
        cerr << "unknown exception" << endl;
        return EXIT_FAILURE;
    }
}

import pstats

def readProfile():
    p = pstats.Stats("result.cprofile")
    p.strip_dirs().sort_stats("cumulative", "name").print_stats(0.5)
    p.strip_dirs().sort_stats("cumulative", "name").print_stats(30)
    p.print_callers(0.5, "ccc")
    p.print_callees("ccc")

if __name__ == "__main__":
    readProfile()

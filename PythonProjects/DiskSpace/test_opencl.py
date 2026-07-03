import os
import opencl4py as cl

if __name__ == "__main__":
    os.environ["PYOPENCL_CTX"] = "0:0"
    platforms = cl.Platforms()
    print("OpenCL devices:\n%s"%platforms.dump_devices())
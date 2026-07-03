import hello_world as hw
import numpy as np
from matplotlib import pyplot as plt 

if __name__ == "__main__":
    print(hw.__sizeOfBytesAsString(10000000))
    e = np.empty([3,2],dtype=complex)
    print(e)

    x=np.arange(32).reshape((8,4))
    print(x)
    print (x[[1,5,7,2]])
    print (x[np.ix_([1,5,7,2],[0,3,1,2])])

    # x = np.arange(1,11) 
    # y =  2  * x +  5 
    # plt.title("Matplotlib demo") 
    # plt.xlabel("x axis caption") 
    # plt.ylabel("y axis caption") 
    # plt.plot(x,y)
    # plt.show()

    # 计算正弦和余弦曲线上的点的 x 和 y 坐标 
    x = np.arange(0,  3  * np.pi,  0.1) 
    y_sin = np.sin(x) 
    y_cos = np.cos(x)  
    # 建立 subplot 网格，高为 2，宽为 1  
    # 激活第一个 subplot
    plt.subplot(2,  1,  1)  
    # 绘制第一个图像 
    plt.plot(x, y_sin) 
    plt.title('Sine')  
    # 将第二个 subplot 激活，并绘制第二个图像
    plt.subplot(2,  1,  2) 
    plt.plot(x, y_cos) 
    plt.title('Cosine')  
    # 展示图像
    plt.show()
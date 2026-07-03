#include <iostream>
#include <string>

int main(){
    //声明命名空间std
    using namespace std;
   
    //定义字符串变量
    string str;
    //定义 int 变量大
    int age;
    //从控制台获取用户输入
    cin>>str>>age;
    //将数据输出到控制台
    cout<<str<<"已经成立"<<age<<"年了！"<<endl;
    return 0;
}
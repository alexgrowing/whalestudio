def removeText(text):
    return text.replace("数学公式:","").replace(" $","$").replace("$ ","$")

s = "令数学公式: $ G $是一个数学公式: $ 25 $阶群。证明数学公式: $ G $至少有一个数学公式: $ 5 $阶子群，且如果它只有一个数学公式: $ 5 $阶子群，则此群是循环群"

print(removeText(s))

import MyProject.Basic
import MyProject.Theorems

def main : IO Unit := do
  IO.println "=== 欢迎来到 Lean 4 项目！==="
  IO.println ""

  -- 基本运算演示
  IO.println "【基本运算】"
  IO.println s!"  double 5     = {double 5}"
  IO.println s!"  factorial 6  = {factorial 6}"
  IO.println s!"  fibonacci 10 = {fibonacci 10}"
  IO.println ""

  -- 列表操作演示
  IO.println "【列表操作】"
  let nums := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]
  IO.println s!"  原始列表: {nums}"
  IO.println s!"  总和: {nums.foldl (· + ·) 0}"
  IO.println s!"  最大值: {nums.foldl Nat.max 0}"
  IO.println ""

  IO.println "Lean 4 项目运行成功！"

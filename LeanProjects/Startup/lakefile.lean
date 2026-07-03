import Lake
open Lake DSL

package «myProject» where

lean_lib «MyProject» where
  -- add library configuration here

@[default_target]
lean_exe «myproject» where
  root := `Main

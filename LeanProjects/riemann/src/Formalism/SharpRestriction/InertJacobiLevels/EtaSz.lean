import Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
import Formalism.SharpRestriction.InertJacobiLevels.TiesAtY

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure Shd0 where
  R : Ranks
  TTn : Finset ℕ
  T2 : Finset ℕ
  q : ℕ
  d : ℕ
  g : Fin 2 → ℕ
  pde : ℕ
  pde' : ℕ
  bits : ℕ → Bool
  etaSz : ℝ
  Sc : ℝ
  hP : ℕ → ℕ
  offS : ℕ → ℕ → ℝ
  kapI : KapI
  ep : ℕ → ℕ

def Shd0.shd (S : Shd0) (sc : Scale) (C : FC) : Shd where
  R := S.R
  TTn := S.TTn
  T2 := S.T2
  q := S.q
  d := S.d
  g := S.g
  pde := S.pde
  pde' := S.pde'
  bits := S.bits
  LaG := G.La C.GK sc
  etaSz := S.etaSz
  Sc := S.Sc
  hP := S.hP
  bs := fun h t => bsVal (2 ^ S.R.e) (h % 2 ^ S.R.e) (t % 2 ^ S.R.e)
  off := offShd S.R S.TTn sc S.offS
  kapI := S.kapI
  ep := S.ep

end Formalism.MainNotions.Inhab

end

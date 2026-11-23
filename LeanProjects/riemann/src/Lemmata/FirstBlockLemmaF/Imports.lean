import Mathlib

namespace Bl.FirstBlockLemmaF

theorem goal1 :
  ∀ (p : Nat) [hp : Fact (Nat.Prime p)] {a b : PadicComplex p} {c : Real},
  LE.le.{0} (Norm.norm.{0} a) c → LE.le.{0} (Norm.norm.{0} b) c → LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) c := by
  intro p hp a b c ha hb
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans (max_le ha ?_)
  rw [norm_neg]
  exact hb

end Bl.FirstBlockLemmaF

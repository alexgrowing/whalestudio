import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff

set_option autoImplicit false

open GlobalTheory GlobalTheory.ProjVar GlobalTheory.CechPic GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjVar.Var

theorem ample_nsmul : ∀ (F : Type) [Field F] (Y : Var F) (Δ : Y.Dv) (n : ℕ), 0 < n → Y.ample Δ → Y.ample (n • Δ) := by
  intro F _ Y Δ n hn h
  have hL := isLB_toLB Δ
  refine (Var.ample_iff_of_toPic_eq (isLB_lbPow hL n) ?_).2 ((isAmpleLB_pow_iff hL hn).2 h)
  rw [cls_lbPow hL, map_nsmul, toPic_apply]

end GlobalTheory.ProjVar.Var

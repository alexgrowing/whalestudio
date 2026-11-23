import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem horiz_eq_xi_red : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (v : Vec K a ι), P.conn v = 0 → v = P.xi (red v) := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ P v hv
  have hn : P.nabla v = 0 := by
    rw [BK.PhiMod.conn_apply] at hv
    exact (smul_right_injective _ PowerSeries.X_ne_zero) (hv.trans (smul_zero _).symm)
  set w := P.xiExt.symm v with hw
  have hvw : v = P.xiExt w := by rw [hw, LinearEquiv.apply_symm_apply]
  have hd : BK.derV w = 0 := by
    rw [hvw, BK.PhiMod.nabla_xiExt, ← map_zero P.xiExt] at hn
    exact P.xiExt.injective hn
  have hnz : ∀ m : ℕ, ((m : K) + 1) ≠ 0 := by
    intro m h
    have h2 : algebraMap ℚ_[l] K ((m : ℚ_[l]) + 1) = 0 := by
      rw [map_add, map_natCast, map_one]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective] at h2
    exact Nat.cast_add_one_ne_zero m h2
  have hc : w = BK.cst (red w) := by
    funext τ i
    ext n
    rcases n with _ | m
    · simp [BK.cst_apply, red_apply]
    · have h1 := congrArg (fun f => PowerSeries.coeff m (f τ i)) hd
      simp only [BK.derV_apply, PowerSeries.coeff_derivative] at h1
      rw [BK.cst_apply, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m)]
      have h3 : PowerSeries.coeff (m + 1) (w τ i) * ((m : K) + 1) = 0 := by simpa using h1
      exact (mul_eq_zero.1 h3).resolve_right (hnz m)
  calc v = P.xiExt w := hvw
    _ = P.xiExt (BK.cst (red w)) := by rw [← hc]
    _ = P.xi (red v) := by rw [BK.PhiMod.xi_apply, hvw, BK.PhiMod.red_xiExt]

end GlobalTheory

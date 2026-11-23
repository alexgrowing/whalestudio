import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

open GlobalTheory.VolBr.NuEq in

theorem val_frame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  intro k _ X _ p P a b σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have hL : CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG
  have hA : CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG'
  set gL := CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y with hgL
  set gA := CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y with hgA
  have hG : gL ^ a * gA ^ b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hL) (zpow_ne_zero _ hA)
  have hGn : (‖gL ^ a * gA ^ b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hG)
  refine ⟨(‖gL ^ a * gA ^ b‖ : ℂ) / (gL ^ a * gA ^ b), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hG)]
  intro f hf
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have hrv : ratVal (P.loc a b f i j) y =
      gL ^ a * gA ^ b * ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y := by
    rw [hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
      ratVal_zpow' uG, ratVal_zpow' uG', eG, eG']
    rfl
  have c0 : 0 < ‖gL‖ := norm_pos_iff.2 hL
  have c0' : 0 < ‖gA‖ := norm_pos_iff.2 hA
  have hexp : Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) =
      ‖gL ^ a * gA ^ b‖⁻¹ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) := by
    rw [(P.L.φ σ).trans i _ y hi hi₀, (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_zpow, norm_zpow,
      ← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
      Real.log_pow, Real.log_pow, ← hgL, ← hgA, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [val, hrv, hexp]
  push_cast
  field_simp

end GlobalTheory.HSAmp

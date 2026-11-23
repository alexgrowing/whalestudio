import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorsionForm

namespace GlobalTheory.PeriodChart

theorem clm_apply_eq_sum {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ b, v b * L (Pi.single b 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : Pi.single b (v b) = v b • (Pi.single b (1 : ℂ) : Fin g → ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [this, map_smul, smul_eq_mul]

theorem matrix_ext_sesq {g : ℕ} {A B : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ z w : Fin g → ℂ, z ⬝ᵥ A *ᵥ star w = z ⬝ᵥ B *ᵥ star w) : A = B := by
  ext a b
  have := h (Pi.single a 1) (Pi.single b 1)
  simpa [Matrix.mulVec_single_one] using this

theorem map_star_mulVec_star {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    M.map star *ᵥ star w = star (M *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.vecMul_transpose]
  rfl

end GlobalTheory.PeriodChart

namespace GlobalTheory.PeriodChart

theorem dualRiemann_half_form_eq : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S)
    (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ (σ : k →+* ℂ) (s : CxPts p σ)
    (τ₀ : Matrix (Fin P.g) (Fin P.g) ℂ) (e : (Fin P.g → ℂ) → CxPts (P.A.hom ≫ p) σ),
    τ₀.IsSymm → (τ₀.map Complex.im).PosDef →
    (∀ d : P.RiemannData s.1, ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
      (∀ z, (d.u.ex (F z)).left ≫ d.φ = (e z).1) ∧
      ∀ z w, HermFrame.form d.H (F z) (F w) = GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm τ₀ z w) →
    ∀ (U : S.Opens) (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W)),
      s ∈ ptsIn p σ U → (h.met σ).form (dUnit P.A hU f) (dUnit P.A hU f') s =
        HermFrame.form ((2 : ℂ) • τ₀.map fun t => (t.im : ℂ))
          (fun a => fderiv ℂ (fun z => ev (P.A.hom ≫ p) σ W f (e z)) 0 (Pi.single a 1))
          (fun a => fderiv ℂ (fun z => ev (P.A.hom ≫ p) σ W f' (e z)) 0 (Pi.single a 1)) := by
  intro k _ S p P h hh σ s τ₀ e hsym hpos hF U W hU f f' hs
  obtain ⟨d⟩ := (hh σ s).1
  obtain ⟨F, hF1, hF2⟩ := hF d
  rw [(hh σ s).2 d U W hU f f' hs]
  set M := LinearMap.toMatrix' F with hM
  have hW : ⊤ ≤ (s.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun x _ => by
    rw [Scheme.Hom.comp_preimage]
    have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    exact hU (mem_ptsIn.1 hs)
  have chain : ∀ q : Γ(P.A.left, W),
      (fun a => fderiv ℂ (fun z => ev (P.A.hom ≫ p) σ W q (e z)) 0 (Pi.single a 1)) =
        d.cov W q ᵥ* M := by
    intro q
    have e1 : (fun z => ev (P.A.hom ≫ p) σ W q (e z)) =
        d.fn W q ∘ (LinearMap.toContinuousLinearMap F) := by
      funext z
      simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
      rw [PPAS.RiemannData.fn, hF1]
      rfl
    have hd : HasFDerivAt (d.fn W q ∘ LinearMap.toContinuousLinearMap F)
        ((fderiv ℂ (d.fn W q) 0).comp (LinearMap.toContinuousLinearMap F)) 0 := by
      have h1 : HasFDerivAt (d.fn W q) (fderiv ℂ (d.fn W q) 0)
          ((LinearMap.toContinuousLinearMap F) 0) := by
        rw [map_zero]
        exact (d.differentiableAt_fn q hW).hasFDerivAt
      exact h1.comp 0 (LinearMap.toContinuousLinearMap F).hasFDerivAt
    funext a
    rw [e1, hd.fderiv, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      clm_apply_eq_sum, Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [PPAS.RiemannData.cov, hM, LinearMap.toMatrix'_apply, mul_comm]
  rw [chain f, chain f']
  set K' : Matrix (Fin P.g) (Fin P.g) ℂ := τ₀.map fun t => (t.im : ℂ) with hK'
  set Q : Matrix (Fin P.g) (Fin P.g) ℂ := (τ₀.map Complex.im)⁻¹.map fun t => (t : ℂ) with hQ
  have hQK : Q * K' = 1 := by
    have hK : K' = (τ₀.map Complex.im).map Complex.ofRealHom := by
      rw [hK', Matrix.map_map]; rfl
    have hQ' : Q = (τ₀.map Complex.im)⁻¹.map Complex.ofRealHom := rfl
    rw [hK, hQ', ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hpos.det_pos.ne'),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hform : Mᵀ * d.H * M.map star = Q := by
    refine matrix_ext_sesq fun z w => ?_
    have h2 := hF2 z w
    rw [← LinearMap.toMatrix'_mulVec F z, ← LinearMap.toMatrix'_mulVec F w, ← hM,
      HermFrame.form, IndefiniteRowSideFullHecke.SiegelReframe.herm] at h2
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, map_star_mulVec_star,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h2, ← Matrix.dotProduct_mulVec]
  have h1 : Mᵀ * (d.H * M.map star * K') = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hform, hQK]
  have h2 : (d.H * M.map star * K') * Mᵀ = 1 := mul_eq_one_comm.1 h1
  have hinv : (((1 / 2 : ℝ) : ℂ) • d.H)⁻¹ = M.map star * ((2 : ℂ) • K') * Mᵀ := by
    refine Matrix.inv_eq_right_inv ?_
    have e2 : M.map star * ((2 : ℂ) • K') * Mᵀ = (2 : ℂ) • (M.map star * K' * Mᵀ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
    norm_num
  have hsymK : K'ᵀ = K' := by
    rw [hK', ← Matrix.transpose_map, hsym]
  rw [HermFrame.dualGram, hinv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, hsymK, HermFrame.form, HermFrame.form, Matrix.star_vecMul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rfl

end GlobalTheory.PeriodChart

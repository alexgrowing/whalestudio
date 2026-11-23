import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex

theorem re_star_dotProduct_self {κ : Type} [Fintype κ] (w : κ → ℂ) :
    (star w ⬝ᵥ w).re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star (w i) * w i).re = Complex.normSq (w i) := by
    simp [Complex.normSq_apply]
  rw [this, Complex.normSq_eq_norm_sq]

theorem re_form_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) (v : κ' → ℂ) :
    (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re = ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
  have h : star v ⬝ᵥ ((Zᴴ * Z) *ᵥ v) = star (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h, Complex.sub_re,
    re_star_dotProduct_self, re_star_dotProduct_self]

theorem posDef_iff {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ ∀ v : κ' → ℂ, v ≠ 0 → ‖WithLp.toLp 2 (Z *ᵥ v)‖ < ‖WithLp.toLp 2 v‖ := by
  have hH : (1 - Zᴴ * Z).IsHermitian :=
    (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)
  constructor
  · intro h v hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv)).1
    have h0 : (0 : ℝ) < ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
      rw [← re_form_eq]
      simpa using hpos
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (sub_pos.mp h0)
  · intro h
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun v hv => ?_⟩
    have hre : 0 < (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re := by
      rw [re_form_eq, sub_pos]
      exact pow_lt_pow_left₀ (h v hv) (norm_nonneg _) two_ne_zero
    have hstar : star (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)) = star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v) := by
      conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
    have him : (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem ballMat_combo {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (s t : Fin n → ℂ) (a b : ℝ) (τ : Ψ) :
    ballMat q (a • s + b • t) τ = a • ballMat q s τ + b • ballMat q t τ := by
  ext x y
  simp [ballMat]

theorem convex_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) [Fintype Ψ] :
    Convex ℝ (ballDom q) := by
  intro s hs t ht a b ha hb hab τ
  refine (posDef_iff _).mpr fun v hv => ?_
  have h1 := (posDef_iff _).mp (hs τ) v hv
  have h2 := (posDef_iff _).mp (ht τ) v hv
  have hc := convex_ball (0 : EuclideanSpace ℂ (Fin j)) ‖WithLp.toLp 2 v‖
    (x := WithLp.toLp 2 (ballMat q s τ *ᵥ v)) (y := WithLp.toLp 2 (ballMat q t τ *ᵥ v))
    (by simpa using h1) (by simpa using h2) ha hb hab
  have he : WithLp.toLp 2 (ballMat q (a • s + b • t) τ *ᵥ v) =
      a • WithLp.toLp 2 (ballMat q s τ *ᵥ v) + b • WithLp.toLp 2 (ballMat q t τ *ᵥ v) := by
    rw [ballMat_combo, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    rfl
  rw [he]
  simpa using hc

theorem zero_mem_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have h : ballMat q (0 : Fin n → ℂ) τ = 0 := by
    ext x y
    simp [ballMat]
  rw [h]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin j') (Fin j') ℂ).PosDef)

theorem ballDom_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n),
    IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q :=
  fun _ _ _ _ _ q => ⟨BallInverse.isOpen_ballDom q, convex_ballDom q, zero_mem_ballDom q⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex

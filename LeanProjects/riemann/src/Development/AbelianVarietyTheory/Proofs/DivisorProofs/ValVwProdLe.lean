import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt GlobalTheory.CovTop
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.CovHt.HTDiag

def LatBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : Host E), letI := H.starRing;
    ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p])
    (P : Point p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left),
    (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) →
    ∀ (τ : E →+* ℂ) (w : P.V), w ∈ htLat c P τ →
      w ∈ Submodule.span ℂ_[p] (P.wRec (embInt c P.integers τ) : Set P.V) →
      ∀ a : ℂ_[p], ‖a‖ ≤ (p : ℝ) ^ (-htEx E p) → a • w ∈ P.wRec (embInt c P.integers τ)

def DiagBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (T : CDVR) (io : c.F →+* T.Fr)
    (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y z : FrPt Xo c ℂ_[p]),
    IsHTFrameCp p y₀ k y → (letI := io.toAlgebra; FrMap k y₀.1 z) →
    ∃ t : Ix Dw → ℂ_[p]ˣ, FrBor t z y ∧ ‖(t none : ℂ_[p])‖ = 1 ∧
      ∀ s, 1 ≤ ‖(t (some s) : ℂ_[p])‖ ∧ ‖(t (some s) : ℂ_[p])‖ ≤ (p : ℝ) ^ htEx E p

end GlobalTheory.CovHt.HTDiag

namespace GlobalTheory.CovHt.HTDiag

theorem val_vw_prod_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (t : Ix Dw → ℂ_[p]ˣ) (ex : Ix Dw → ℤ) (h : ℝ) (h0 : ex none = 0)
    (ht : ∀ s, 1 ≤ ‖(t (some s) : ℂ_[p])‖ ∧ ‖(t (some s) : ℂ_[p])‖ ≤ (p : ℝ) ^ h) (he : 0 ≤ (vLa la (p : K) : ℝ))
    (hh : 0 ≤ h) :
    val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) ((∏ i, t i ^ ex i : ℂ_[p]ˣ) : ℂ_[p]) ≤
      (((vLa la (p : K) : ℝ) * h * ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |(ex (some s) : ℝ)| : ℝ) : EReal) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  rw [val_vw_of_ne la p _ (Units.ne_zero _), EReal.coe_le_coe_iff,
    GlobalTheory.PadicComplexHost.valuation_coe_eq_norm, GlobalTheory.PadicComplexHost.valuation_coe_eq_norm,
    GlobalTheory.PadicComplexHost.norm_p, Real.log_inv, Units.coe_prod, norm_prod, Real.log_prod]
  · simp only [Units.val_zpow_eq_zpow_val, norm_zpow, Real.log_zpow, Fintype.sum_option, h0, Int.cast_zero, zero_mul,
      zero_add]
    rw [_root_.mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ he
    rw [div_neg, ← neg_div, ← Finset.sum_neg_distrib, div_le_iff₀ hlp, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    obtain ⟨h1, h2⟩ := ht s
    have hl0 : 0 ≤ Real.log ‖(t (some s) : ℂ_[p])‖ := Real.log_nonneg h1
    have hl1 : Real.log ‖(t (some s) : ℂ_[p])‖ ≤ h * Real.log p := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) h2
    have := neg_abs_le (ex (some s) : ℝ)
    nlinarith [abs_nonneg (ex (some s) : ℝ)]
  · intro i _
    exact norm_ne_zero_iff.2 (t i ^ ex i).ne_zero

end GlobalTheory.CovHt.HTDiag

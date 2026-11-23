import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricEqConstMulRiemannFormOnExpChartStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.PerChart

theorem exists_periodChart_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, d, hP, hE, hx₀, h0, hcard, hd, hInner, hR⟩ :=
    GlobalTheory.T.exists_riemannForm_periodChart_genericFibre E H Dw l Xo c O β Y T σ U hσ hU x₀
  obtain ⟨κ, hκ, hM⟩ := GlobalTheory.T.hodgeMetric_eq_const_mul_riemannForm_on_expChart E H Dw l Xo c O β Y T σ U hσ hU n a ha g ch₀ ex hE hcard hInner
  refine ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, fun τ => κ τ * d, hP, hE, hx₀, h0, hcard,
    fun τ => mul_pos (hκ τ) hd, hInner, ?_⟩
  intro x hx hin f W hW
  obtain ⟨h1, h2⟩ := hM x hx hin _ (hR x hx hin) f W hW
  have hs : ∀ (M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ),
      hermForm (((d : ℝ) : ℂ) • M) v w = ((d : ℝ) : ℂ) * hermForm M v w := by
    intro M v w
    simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · rw [h1 τ]
    ext b b'
    simp only [Matrix.smul_apply, Matrix.of_apply, hs, smul_eq_mul]
    push_cast
    ring
  · have := h2 p q hpq
    rw [hs] at this
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd.ne')

end GlobalTheory.ShFam.Hor.PerChart

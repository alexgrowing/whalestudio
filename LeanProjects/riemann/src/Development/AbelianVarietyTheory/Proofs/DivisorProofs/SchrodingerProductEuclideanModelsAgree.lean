import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.Proof.schrodinger_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  intro l _ _ w φ f f₁ hf hf₁
  obtain ⟨p, q⟩ := w
  have h : ⇑f₁ = rhoFun (Sum.elim p q) ⇑f := by
    funext x
    rw [hf₁, GlobalTheory.Published.Metaplectic.rho_apply, rhoFun, hf]
    simp only [phase, pPart, qPart, Sum.elim_inl, Sum.elim_inr, PiLp.inner_apply, WithLp.ofLp_add]
    congr 1
    · congr 1
      push_cast
      simp only [dotProduct, RCLike.inner_apply, conj_trivial, Finset.sum_div]
      push_cast
      ring_nf
      rw [Finset.sum_congr rfl fun i _ => mul_comm ((q i : ℝ) : ℂ) ((p i : ℝ) : ℂ)]
      ring
  refine Lp.ext ((f₁.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho _ _).trans (rhoFun_congr _ (f.coeFn_toLp 2 volume))).symm

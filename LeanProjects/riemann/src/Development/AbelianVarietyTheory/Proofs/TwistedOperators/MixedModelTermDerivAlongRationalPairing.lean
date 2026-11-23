import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivativeIsotropicDirectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

namespace GlobalTheory.MixedTerm.DerLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_tauE_add_conj (D : D7) (e : D.host.E) :
    ∑ t, (tauE D t e + starRingEnd ℂ (tauE D t e)) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [Finset.sum_add_distrib, h4]

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  rw [← sum_tauE_add_conj]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem trace_map_mul (D : D7) (τ : D.what₂.Tau) {m n : ℕ} (P : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (P.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (P * x)) := by
  rw [← Matrix.map_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem term_derAlong : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG x y
  have hlin := GlobalTheory.T.mixedModelTerm_linear_thetaFunctions D V V' W r C C' B ψ hψ μ 𝓨 hcov y
  have hder := fun τ => GlobalTheory.T.mixedModelTerm_derivative_isotropicDirection D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG τ (x.map (tauE D τ)) y
  set f : D.what₂.Tau → WO V W → ℂ :=
    fun τ => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G with hf
  have hft : ∀ τ, IsThetaFunO ψ V W (f τ) := fun τ => GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hG
  have hsum : ∀ s : Finset D.what₂.Tau,
      term ψ V V' W C C' B μ 𝓨 (∑ τ ∈ s, f τ) y = ∑ τ ∈ s, term ψ V V' W C C' B μ 𝓨 (f τ) y := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hlin.2 0 G hG
      rw [zero_smul, zero_mul] at h0
      simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hlin.1 _ _ (hft a) (GlobalTheory.Size.theta_finsetSum s fun i _ => hft i), ih]
  show term ψ V V' W C C' B μ 𝓨 (∑ τ, f τ) y = _
  rw [hsum, Finset.sum_congr rfl fun τ _ => hder τ, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  simp only [trace_map_mul, sum_two_re_tauE, ratPair, Complex.ofReal_ratCast]

end GlobalTheory.MixedTerm.DerLaw

end

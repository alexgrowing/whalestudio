import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelLie

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem Eop_add_conjugate (τ : E →+* ℂ) (i : Fin a) :
    Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  simp only [Eop, e1, e2, map_neg]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (1 + 1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) (1 : ℂ) := fun τ => by
    unfold atEmb
    split_ifs <;> simp
  funext w
  simp only [e, Finset.sum_apply, Pi.single_apply, Pi.add_apply, Pi.one_apply]
  simp only [eq_comm (a := w)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    IsTotallyComplex.mult_eq]
  norm_num

theorem sum_Eop_diag (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  have hs : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i i = ∑ τ : E →+* ℂ, Eop τ i i :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (fun τ : E →+* ℂ => star_star τ))
      (fun τ => Eop τ i i)
  have h : (∑ τ : E →+* ℂ, Eop τ i i) + ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 + lieS E a i i 1 := by
    nth_rw 2 [← hs]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conjugate τ i, ← map_sum,
      sum_atEmb_one, map_add]
  have h2 : (2 : ℂ) • (∑ τ : E →+* ℂ, Eop τ i i) = (2 : ℂ) • lieS E a i i 1 := by
    rw [two_smul, two_smul, h]
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

theorem lie_oneL_eq_sum_Eop (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop_diag i]
  simp only [lieS_apply]
  rw [← map_sum]
  have hm : ∑ i : Fin a, Matrix.single i i (1 : Cinf E) = 1 := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp [Matrix.single_apply]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  congr 1
  exact (congrArg Matrix.of.symm hm).symm

end GlobalTheory.CompanionTheory.ClozelLie

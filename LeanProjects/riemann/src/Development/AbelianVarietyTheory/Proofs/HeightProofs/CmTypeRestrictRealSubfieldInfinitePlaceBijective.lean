import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMTypePlaces

open NumberField

theorem mk_tauE_bijective (D : D7) :
    Function.Bijective fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ) := by
  obtain ⟨hb, hm⟩ := Formalism.BasicNotions.factEmb D.R D.host
  have hsq := D.host.sqd_sq
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have hmem : ∀ τ : D.what₂.Tau, tauE D τ (D.host.sqd) =
      Complex.I * (Real.sqrt D.host.d : ℂ) := fun τ => (hm _).2 (D.eTau τ).2
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by
    have : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hdpos)).ne'
    exact_mod_cast this
  have hconj : (starRingEnd ℂ) (Complex.I * (Real.sqrt D.host.d : ℂ)) =
      -(Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hsurj : ∀ φ : D.host.E →+* ℂ, φ (D.host.sqd) =
      Complex.I * (Real.sqrt D.host.d : ℂ) → ∃ τ, tauE D τ = φ := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := hb.2 φ
    refine ⟨D.eTau.symm ⟨g, (hm g).1 hφ⟩, ?_⟩
    simp only [tauE, Equiv.apply_symm_apply]
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact D.eTau.injective (Subtype.ext (hb.1 h))
    · exfalso
      have h1 := congrArg (fun φ : D.host.E →+* ℂ => φ (D.host.sqd)) h
      simp only [ComplexEmbedding.conjugate_coe_eq] at h1
      rw [hmem, hmem, hconj] at h1
      have h2 : Complex.I * (Real.sqrt D.host.d : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h1
      exact mul_ne_zero Complex.I_ne_zero hs h2
  · intro w
    have h1 : (w.embedding (D.host.sqd)) ^ 2 =
        (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hd0]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · obtain ⟨τ, hτ⟩ := hsurj _ h
      exact ⟨τ, by simp only [hτ, InfinitePlace.mk_embedding]⟩
    · obtain ⟨τ, hτ⟩ := hsurj (ComplexEmbedding.conjugate w.embedding) (by
        rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, hconj, neg_neg])
      exact ⟨τ, by simp only [hτ, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem places_bijective : ∀ D : D7, Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) := by
  intro D
  haveI := D.host.isCMField_hostE
  exact (IsCMField.equivInfinitePlace D.host.E).bijective.comp (mk_tauE_bijective D)

end GlobalTheory.CMTypePlaces

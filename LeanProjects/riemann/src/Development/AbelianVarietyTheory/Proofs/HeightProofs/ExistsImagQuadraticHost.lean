import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem exists_hostK : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (_ : IsTotallyComplex K), Module.finrank ℚ K = 2 ∧ discr K = -(H.d : ℤ) ∧ discr K < -4 ∧ K ≤ H.φ₀.toRatAlgHom.fieldRange ∧ (∀ z : ℂ, (∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + H.φ₀ H.sqrtMinusD) / 2)) ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) ∧ Module.finrank ℚ H.E = 2 * R.f := by
  intro R H
  obtain ⟨-, hd, -, hd16, -⟩ := H.hyp
  have hb : (H.φ₀ H.sqrtMinusD) ^ 2 = -(H.d : ℂ) := by
    have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq
    rw [← map_pow, h, map_neg, map_natCast]
  let σ : H.K →ₐ[ℚ] ℂ := H.φ₀.toRatAlgHom.comp H.K.val
  let e : H.K ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  have hfd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  have hNF : NumberField σ.fieldRange := NumberField.mk
  have h2 : Module.finrank ℚ σ.fieldRange = 2 :=
    e.toLinearEquiv.finrank_eq.symm.trans
      (Formalism.FrobeniusOrbits.SplitK.finrank_K hd.pos (H.sqd_sq))
  let r : σ.fieldRange := ⟨H.φ₀ H.sqrtMinusD, ⟨Formalism.FrobeniusOrbits.SplitK.bK H.sqrtMinusD, rfl⟩⟩
  have hr : r ^ 2 = -(H.d : σ.fieldRange) := by
    apply Subtype.ext
    simpa [r] using hb
  have h4 : H.d % 4 = 3 := by omega
  have hD : discr σ.fieldRange = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 hd.squarefree h4 hr
  have hTC : IsTotallyComplex σ.fieldRange := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    let ψ := InfinitePlace.embedding_of_isReal hv
    have h1 : ψ r ^ 2 = -(H.d : ℝ) := by rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg (ψ r)]
  obtain ⟨x, -, hx, -, hgen, -⟩ := ringOfIntegers_sqrt_neg_three_mod_four H.d hd.squarefree h4 σ.fieldRange h2 r hr
  have hx' : ((x : σ.fieldRange) : ℂ) = (1 + H.φ₀ H.sqrtMinusD) / 2 := by
    have := congrArg (fun y : σ.fieldRange => (y : ℂ)) hx
    simp only [r] at this
    push_cast at this
    have e2 : ((2 : σ.fieldRange) : ℂ) = 2 := rfl
    rw [e2] at this
    linear_combination this / 2
  have hc : ∀ m n : ℤ, ((((m : 𝓞 σ.fieldRange) + n * x : 𝓞 σ.fieldRange) : σ.fieldRange) : ℂ) =
      m + n * ((1 + H.φ₀ H.sqrtMinusD) / 2) := fun m n => by
    rw [← hx']
    simp
  refine ⟨σ.fieldRange, hNF, hTC, h2, hD, by omega, ?_, fun z => ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(y : H.E), rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, hc s.1 s.2⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨m, n, rfl⟩ := hgen a
    exact ⟨(m, n), hc m n⟩
  · rw [H.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring

end GlobalTheory.FieldSize

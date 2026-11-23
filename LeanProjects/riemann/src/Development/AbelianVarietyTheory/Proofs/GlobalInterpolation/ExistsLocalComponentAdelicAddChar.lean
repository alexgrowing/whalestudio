import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.LocalComponentChar

open Classical in

theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem index_intV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (LocalAdditiveCharacterDual.intV F v).index = 0 := by
  by_contra hn
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (1 : ℤ))
  have hn' : (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := (LocalAdditiveCharacterDual.intV F v).nsmul_index_mem (t / (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v))
  rw [nsmul_eq_mul, mul_div_cancel₀ _ hn'] at h
  have h1 : Valued.v t ≤ 1 := h
  rw [ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_localChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  intro F _ _ ψ hψ v hfin
  refine ⟨⟨psiV F ψ v, LocalAdditiveCharacterDual.psiV_zero F ψ v, LocalAdditiveCharacterDual.psiV_add F ψ v⟩, ⟨?_, fun t => hψ.2.1 _, ?_⟩,
    fun _ => rfl⟩
  · have h2 : Continuous fun x : Fv F v => pairA F 0 (singleV F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV F v)
    exact hψ.1.comp h2
  · by_contra h
    push Not at h
    have htop : LocalAdditiveCharacterDual.psiDual F ψ v = ⊤ := by
      rw [eq_top_iff]
      intro t _ s _
      exact h _
    apply hfin.1
    rw [htop, AddSubgroup.relIndex_top_right]
    exact index_intV F v

end GlobalTheory.LocalComponentChar

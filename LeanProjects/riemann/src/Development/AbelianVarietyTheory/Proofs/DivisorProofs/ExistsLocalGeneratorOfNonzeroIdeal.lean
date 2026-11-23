import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open IsDedekindDomain HeightOneSpectrum WithZero

theorem locGen_val_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = v.intValuation d := by
  have h := valuedAdicCompletion_eq_valuation' (K := F) v (d : F)
  rw [← valuation_of_algebraMap (K := F) v d]
  exact h

theorem ideal_localGenerator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  intro F _ _ I v hI
  by_cases hv : I ≤ v.asIdeal
  · classical
    have hex : ∃ n : ℕ, ∃ d ∈ I, v.intValuation d = exp (-(n : ℤ)) := by
      obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨_, d, hdI, v.intValuation_if_neg hd0⟩
    obtain ⟨d0, hd0I, hd0v⟩ := Nat.find_spec hex
    refine ⟨algebraMap F _ (d0 : F), ?_, fun h => absurd hv h, ?_, d0, hd0I, rfl⟩
    · intro h
      have h2 := locGen_val_eq F v d0
      rw [h, map_zero, hd0v] at h2
      exact exp_ne_zero h2.symm
    · intro d hd
      rw [locGen_val_eq, locGen_val_eq, hd0v]
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hk := v.intValuation_if_neg hd0
        rw [hk, exp_le_exp, neg_le_neg_iff, Int.ofNat_le]
        exact Nat.find_min' hex ⟨d, hd, hk⟩
  · obtain ⟨d, hdI, hdv⟩ := Set.not_subset.mp hv
    refine ⟨1, one_ne_zero, fun _ => rfl, ?_, d, hdI, ?_⟩
    · intro e _
      rw [locGen_val_eq, map_one]
      exact v.intValuation_le_one e
    · rw [locGen_val_eq, map_one]
      exact intValuation_eq_one_iff.mpr hdv

end GlobalTheory

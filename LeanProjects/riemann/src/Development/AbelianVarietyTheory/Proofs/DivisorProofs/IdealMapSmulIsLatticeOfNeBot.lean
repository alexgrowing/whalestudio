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

open scoped Pointwise

namespace GlobalTheory

theorem ideal_map_smul_isLattice (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) :
    I ≠ ⊥ → Submodule.IsLattice E L →
      Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  intro hI hL
  have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) • L ≤ L := Submodule.smul_le_right
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hdE : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hd0
    have h1 : algebraMap (𝓞 F) (𝓞 E) d = 0 := by exact_mod_cast h
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h1)
  set u : Eˣ := Units.mk0 _ hdE
  have hsub : (u • L : Submodule (𝓞 E) (Fin n → E)) ≤ I.map (algebraMap (𝓞 F) (𝓞 E)) • L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have : (u • y : Fin n → E) = (algebraMap (𝓞 F) (𝓞 E) d) • y := by
      rw [Units.smul_def, Units.val_mk0, ← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) d) y]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hdI) hy
  exact Submodule.IsLattice.of_le_of_isLattice_of_fg E hsub (Submodule.FG.of_le hL.fg hle)

end GlobalTheory

import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKsEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegL

open Polynomial

theorem natDegree_minpoly_sqrt (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (y : Om l)
    (hF : F ≤ MaximalUnramifiedExtension l) (hy : y ^ 2 = -(l : Om l)) (hyK : y ∉ MaximalUnramifiedExtension l) :
    (minpoly F y).natDegree = 2 := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have hmon : (X ^ 2 + C ((l : ℕ) : F)).Monic :=
    (monic_X_pow 2).add_of_left (degree_C_le.trans_lt (by simp))
  have hdeg : (X ^ 2 + C ((l : ℕ) : F)).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  have hev : aeval y (X ^ 2 + C ((l : ℕ) : F)) = 0 := by
    simp [hy]
  have h1 : (minpoly F y).natDegree ≤ 2 :=
    hdeg ▸ natDegree_le_natDegree (minpoly.min F y hmon hev)
  have h2 : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have h3 : (minpoly F y).natDegree ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp h
    apply hyK
    rw [← ha]
    exact hF a.2
  omega

theorem structure_sqrt_neg : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  intro l _ hl2 K M y hM hy hyK hyz hK
  have hyK1 : y ∈ K.1 := hK ▸ (le_sup_right : IntermediateField.adjoin ℚ_[l] {y} ≤ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  have hMK0 : M ≤ K0 K := le_inf (hK ▸ le_sup_left) hM
  have hA : IntermediateField.adjoin ℚ_[l] {y} ≤ K.1 :=
    (IntermediateField.adjoin_simple_le_iff).2 hyK1
  have e1 : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} :=
    le_antisymm (hK.le.trans (sup_le_sup_right hMK0 _)) (sup_le inf_le_left hA)
  have e2 : K.1 ≤ Ks K 1 := by
    rw [e1]
    exact sup_le_sup_left ((IntermediateField.adjoin_simple_le_iff).2 hyz) _
  have hd := natDegree_minpoly_sqrt l (K0 K) y inf_le_right hy hyK
  have hf : Module.finrank ℚ_[l] ↥K.1 = Module.finrank ℚ_[l] ↥(K0 K) * 2 := by
    rw [← hd, ← GlobalTheory.HubLoc.finrank_sup_adjoin, ← e1]
  have hpos := GlobalTheory.HubLoc.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have := K.2
  have htow := Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1
  have e3 : Module.finrank ↥(K0 K) ↥K.1 = 2 := by
    rw [hf] at htow
    exact Nat.eq_of_mul_eq_mul_left hpos htow
  refine ⟨e1, e2, e3, ?_⟩
  rw [GlobalTheory.HubLoc.finrank_Ks_eq l K 1 one_pos, hf]
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  have hev : 2 ∣ l - 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  rw [Nat.sub_self, pow_zero, one_mul]
  rw [Nat.mul_div_cancel_left k two_pos]
  ring

end GlobalTheory.SqrtNegL

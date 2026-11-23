import Mathlib
import GroundTheory.GlobalFields.Artin.Induction
import GroundTheory.GlobalFields.Artin.SeriesEuler
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain IntermediateField GroundTheory.LocalField

namespace GroundTheory.Global.Artin

theorem dedekindZeta_congr {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (e : F ≃+* F') : dedekindZeta F = dedekindZeta F' := by
  set f := RingOfIntegers.mapRingEquiv e
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Ideal.relIsoOfBijective f.symm.toRingHom f.symm.bijective).toEquiv fun I ↦ ?_)
  change Ideal.absNorm I = n ↔ Ideal.absNorm (I.comap f.symm.toRingHom) = n
  have h : Ideal.absNorm (I.comap f.symm.toRingHom) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv I (I.comap f.symm.toRingHom) f
      (by rw [Ideal.map_comap_of_equiv]; rfl)).toEquiv.symm
  rw [h]

section Regular

variable {G : Type*} [Group G]

section Finite

variable [Fintype G]

theorem indFun_bot_one [Fintype (⊥ : Subgroup G)] :
    indFun (⊥ : Subgroup G).subtype 1 = (Representation.leftRegular ℂ G).character := by
  classical
  funext g
  rw [indFun_apply, character_leftRegular_apply, Subgroup.card_bot, Nat.cast_one, inv_one, one_mul]
  have h : ∀ t : G, (∑ h : (⊥ : Subgroup G),
      if ((⊥ : Subgroup G).subtype h) = t⁻¹ * g * t then (1 : (⊥ : Subgroup G) → ℂ) h else 0) =
      if g = 1 then 1 else 0 := fun t ↦ by
    rw [Fintype.sum_unique]
    have : ((⊥ : Subgroup G).subtype (default : (⊥ : Subgroup G))) = 1 := rfl
    rw [this, Pi.one_apply]
    by_cases hg : g = 1
    · simp [hg]
    · rw [if_neg hg, if_neg]
      intro h1
      apply hg
      have := congrArg (fun x ↦ t * x * t⁻¹) h1
      simpa [mul_assoc] using this.symm
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  split_ifs <;> simp

end Finite

variable (G) in

def charDegree (χ : G → ℂ) : ℕ := ⌊(χ 1).re⌋₊

end Regular

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [IsGalois K L] in

theorem fixedFieldFun_one (H : Subgroup Gal(L/K)) : fixedFieldFun H (1 : H → ℂ) = 1 := rfl

theorem artinL_leftRegular [Fintype Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    artinL K L (Representation.leftRegular ℂ Gal(L/K)).character s = dedekindZeta L s := by
  classical
  have h1 : IsClassFun (1 : (⊥ : Subgroup Gal(L/K)) → ℂ) := fun _ _ ↦ rfl
  rw [← indFun_bot_one, artinL_indFun (⊥ : Subgroup Gal(L/K)) h1 hs, fixedFieldFun_one,
    artinL_one hs]
  exact congrFun (dedekindZeta_congr ((equivOfEq (fixedField_bot (F := K) (E := L))).trans
    topEquiv).toRingEquiv) s

end GroundTheory.Global.Artin

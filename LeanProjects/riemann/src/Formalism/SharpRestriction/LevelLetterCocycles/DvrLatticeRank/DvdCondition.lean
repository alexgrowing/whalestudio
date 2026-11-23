import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.FinrankMaxUnramifiedSubfieldPadicFinExtPos

noncomputable section

namespace Formalism.MainNotions.N.Ln34.DvdPf

open Formalism.BasicNotions Formalism.BasicNotions.Loc Module

private theorem finrank_cyclotomicExt_dvd_sub_one {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsIntegral F Ω] (E K : IntermediateField F Ω) (hEK : E ≤ K) (l : ℕ) (hp : l.Prime)
    (hle : K ≤ E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1}) :
    Module.finrank E (IntermediateField.extendScalars hEK) ∣ l - 1 := by
  have hl0 : 0 < l := hp.pos
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : NeZero (l : E) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : Algebra.IsIntegral E Ω := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := F) x).tower_top⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ l := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l Ω)
      (Polynomial.degree_cyclotomic_pos l Ω hl0).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  set M : IntermediateField E Ω := IntermediateField.adjoin E {ζ} with hM
  haveI hcyc : IsCyclotomicExtension {l} E M := by
    first
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension E
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension
    | exact IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension E hζ
  haveI : FiniteDimensional E M := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hl0).tower_top
    | exact IsCyclotomicExtension.finiteDimensional {l} E M
  haveI : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M

  have hcard : Module.finrank E M ∣ l - 1 := by
    have hμ := IsCyclotomicExtension.zeta_spec l E M
    have hinj := IsPrimitiveRoot.autToPow_injective E hμ
    have h1 : Nat.card (M ≃ₐ[E] M) ∣ Nat.card (ZMod l)ˣ := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (M ≃ₐ[E] M) = Module.finrank E M := by
      first
      | exact IsGalois.card_aut_eq_finrank E M
      | (rw [Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank E M)
    have h3 : Nat.card (ZMod l)ˣ = l - 1 := by
      haveI : Fact l.Prime := ⟨hp⟩
      first
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units])
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp])
    rw [← h2, ← h3]
    exact h1

  have hsup : E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1} ≤ M.restrictScalars F := by
    apply sup_le
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact M.algebraMap_mem ⟨y, hy⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      have hζM : ζ ∈ M := IntermediateField.mem_adjoin_simple_self E ζ
      show y ∈ M.restrictScalars F
      rw [IntermediateField.mem_restrictScalars]
      first
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
         exact pow_mem hζM i)
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy' hl0
         exact pow_mem hζM i)
  have hKM : IntermediateField.extendScalars hEK ≤ M := by
    intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    exact (IntermediateField.mem_restrictScalars F).mp (hsup (hle hx))

  have hdvd : Module.finrank E (IntermediateField.extendScalars hEK) ∣ Module.finrank E M := by
    first
    | (have h := IntermediateField.relfinrank_mul_relfinrank
          (bot_le : (⊥ : IntermediateField E Ω) ≤ IntermediateField.extendScalars hEK) hKM
       rw [IntermediateField.relfinrank_bot_left, IntermediateField.relfinrank_bot_left] at h
       exact Dvd.intro _ h)
    | exact IntermediateField.finrank_dvd_of_le_right hKM
  exact hdvd.trans hcard

theorem dvdCondition : Formalism.MainNotions.N.Ln34.DvdStep := by
  intro l _ hl K LL hG
  have hle : K.1 ≤ Ks K 1 := hG.2.2.1
  have hEK : K0 K ≤ K.1 := inf_le_left
  haveI : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have h := finrank_cyclotomicExt_dvd_sub_one (F := ℚ_[l]) (K0 K) K.1 hEK l (Fact.out) hle
  first
  | exact h
  | (show Module.finrank (K0 K) K.1 ∣ l - 1
     convert h using 1
     exact LinearEquiv.finrank_eq
       { toFun := fun y => ⟨y.1, y.2⟩
         invFun := fun y => ⟨y.1, y.2⟩
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl })

end Formalism.MainNotions.N.Ln34.DvdPf

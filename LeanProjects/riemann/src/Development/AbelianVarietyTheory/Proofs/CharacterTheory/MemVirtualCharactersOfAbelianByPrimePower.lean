import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvdStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterExtendScalarsRep
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunctionStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsAbelianByPrimePowerNotDvdCardFixedByStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndRestrictEqCardFixedByMulStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharactersStatement

noncomputable section
namespace GlobalTheory.BI

theorem mem_virt_of_forall_abByP (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    [CharZero L] (G : Type) [Group G] [Finite G]
    (hH : ∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) :
    ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  let S : AddSubgroup (G → ℤ) :=
    { carrier := {f | ∀ χ : G → L, IsChar L L χ → (fun g => (f g : L) * χ g) ∈ Virt K L G}
      zero_mem' := by
        intro χ _
        have : (fun g => (((0 : G → ℤ) g : ℤ) : L) * χ g) = 0 := by
          funext g; simp
        rw [this]; exact zero_mem _
      add_mem' := by
        intro a b ha hb χ hχ
        have : (fun g => (((a + b) g : ℤ) : L) * χ g)
            = (fun g => (a g : L) * χ g) + (fun g => (b g : L) * χ g) := by
          funext g; simp [add_mul]
        rw [this]; exact add_mem (ha χ hχ) (hb χ hχ)
      neg_mem' := by
        intro a ha χ hχ
        have : (fun g => (((-a) g : ℤ) : L) * χ g) = -(fun g => (a g : L) * χ g) := by
          funext g; simp
        rw [this]; exact neg_mem (ha χ hχ) }
  have hS : ∀ f : G → ℤ, f ∈ S ↔
      ∀ χ : G → L, IsChar L L χ → (fun g => (f g : L) * χ g) ∈ Virt K L G := fun _ => Iff.rfl
  have hmul : ∀ f ∈ S, ∀ f' ∈ S, f * f' ∈ S := by
    intro f hf f' hf'
    rw [hS] at hf hf' ⊢
    intro χ hχ
    obtain ⟨a, b, ha, hb, hab⟩ := (GlobalTheory.T.mem_virtualCharacters_iff_sub_characters K L G _).1 (hf' χ hχ)
    have : (fun g => (((f * f') g : ℤ) : L) * χ g)
        = (fun g => (f g : L) * a g) - (fun g => (f g : L) * b g) := by
      funext g
      have h := congrFun hab g
      simp only [Pi.sub_apply] at h
      simp only [Pi.mul_apply, Pi.sub_apply, Int.cast_mul]
      rw [mul_assoc, h, mul_sub]
    rw [this]
    exact sub_mem (hf a (GlobalTheory.BI.isChar_baseChange K L G a ha)) (hf b (GlobalTheory.BI.isChar_baseChange K L G b hb))
  have hperm : ∀ H : Subgroup G, AbByP H →
      (fun g => (Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℤ)) ∈ S := by
    intro H hA
    rw [hS]
    intro χ hχ
    obtain ⟨hres, hconj, -⟩ := GlobalTheory.isChar_restrict_conj_one L L G χ hχ
    have h1 : IsChar K L (fun h : H => χ h) := hH H hA _ (hres H H.subtype)
    have h2 := GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction K L G H _ h1
    have : (fun g => (((Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℤ)) : L) * χ g)
        = ind H (fun h : H => χ h) := by
      funext g
      rw [GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn L G H χ hconj g, Int.cast_natCast]
    rw [this]
    exact AddSubgroup.subset_closure h2
  have hone : (1 : G → ℤ) ∈ S := by
    refine GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd G S hmul fun x p hp => ?_
    obtain ⟨H, hA, hp'⟩ := GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy G x p hp
    exact ⟨_, hperm H hA, fun h => hp' (Int.natCast_dvd_natCast.1 h)⟩
  intro χ hχ
  simpa using (hS 1).1 hone χ hχ

end GlobalTheory.BI

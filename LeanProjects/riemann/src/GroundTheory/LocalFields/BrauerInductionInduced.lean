import Mathlib
import GroundTheory.LocalFields.BrauerInductionCharacters

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section IndFun

variable {G H K : Type*} [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]

open Classical in

def indFun (φ : H →* G) : (H → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun ψ s := (Nat.card H : ℂ)⁻¹ * ∑ t : G, ∑ h : H, if φ h = t⁻¹ * s * t then ψ h else 0
  map_add' ψ ψ' := by
    funext s
    simp only [Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    split_ifs <;> simp
  map_smul' c ψ := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_left_comm c]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    split_ifs <;> simp

open Classical in
theorem indFun_apply (φ : H →* G) (ψ : H → ℂ) (s : G) :
    indFun φ ψ s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, ∑ h : H, if φ h = t⁻¹ * s * t then ψ h else 0 := rfl

theorem indFun_apply_one (φ : H →* G) (hφ : Function.Injective φ) (ψ : H → ℂ) :
    indFun φ ψ 1 = (Nat.card G : ℂ) / Nat.card H * ψ 1 := by
  classical
  rw [indFun_apply]
  have h1 : ∀ t : G, ∑ h : H, (if φ h = t⁻¹ * 1 * t then ψ h else 0) = ψ 1 := by
    intro t
    have hiff : ∀ h : H, φ h = t⁻¹ * 1 * t ↔ h = 1 := fun h ↦ by
      rw [show t⁻¹ * 1 * t = 1 by group, ← map_one φ]
      exact hφ.eq_iff
    simp_rw [hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  ring

theorem isClassFun_indFun (φ : H →* G) (ψ : H → ℂ) : IsClassFun (indFun φ ψ) := by
  classical
  intro s k
  rw [indFun_apply, indFun_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft k⁻¹) _ _ fun t ↦ ?_
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp only [Equiv.coe_mulLeft]
  congr 1
  apply propext
  rw [show (k⁻¹ * t)⁻¹ * s * (k⁻¹ * t) = t⁻¹ * (k * s * k⁻¹) * t by group]

theorem charInner_indFun (φ : H →* G) (ψ : H → ℂ) {χ : G → ℂ} (hχ : IsClassFun χ) :
    charInner G (indFun φ ψ) χ = charInner H ψ (χ ∘ φ) := by
  classical
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hinner : ∀ (t : G) (h : H),
      ∑ s : G, (if φ h = t⁻¹ * s * t then ψ h else 0) * χ s⁻¹ = ψ h * χ (φ h⁻¹) := by
    intro t h
    have hiff : ∀ s : G, (φ h = t⁻¹ * s * t) ↔ (s = t * φ h * t⁻¹) := by
      intro s
      constructor
      · rintro hs
        rw [hs]
        group
      · rintro rfl
        group
    simp_rw [ite_mul, zero_mul, hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    congr 1
    rw [show (t * φ h * t⁻¹)⁻¹ = t * φ h⁻¹ * t⁻¹ by simp [mul_assoc], hχ]
  have hpt : ∀ s : G, indFun φ ψ s * χ s⁻¹ = (Nat.card H : ℂ)⁻¹ * ∑ t : G, ∑ h : H,
      (if φ h = t⁻¹ * s * t then ψ h else 0) * χ s⁻¹ := by
    intro s
    rw [indFun_apply, mul_assoc, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
  have hsum : ∑ s : G, indFun φ ψ s * χ s⁻¹ =
      (Nat.card H : ℂ)⁻¹ * (Nat.card G * ∑ h : H, ψ h * χ (φ h⁻¹)) := by
    rw [Finset.sum_congr rfl fun s _ ↦ hpt s, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl fun t _ ↦ (Finset.sum_comm.trans (Finset.sum_congr rfl fun h _ ↦ hinner t h)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [charInner_apply, hsum, charInner_apply]
  simp only [Function.comp_apply]
  field_simp

theorem charInner_indFun_right (φ : H →* G) (ψ : H → ℂ) {χ : G → ℂ} (hχ : IsClassFun χ) :
    charInner G χ (indFun φ ψ) = charInner H (χ ∘ φ) ψ := by
  rw [charInner_comm, charInner_indFun φ ψ hχ, charInner_comm]

omit [Fintype G] [Fintype H] in

theorem IsClassFun.comp {χ : G → ℂ} (hχ : IsClassFun χ) (φ : H →* G) : IsClassFun (χ ∘ φ) := by
  intro h k
  simp only [Function.comp_apply, map_mul, map_inv]
  exact hχ _ _

theorem indFun_indFun (φ : H →* G) (φ' : K →* H) (ψ : K → ℂ) :
    indFun φ (indFun φ' ψ) = indFun (φ.comp φ') ψ := by
  apply eq_of_isClassFun_of_charInner (isClassFun_indFun _ _) (isClassFun_indFun _ _)
  intro χ hχ
  have hcl := (mem_irrChars.mp hχ).isCharacter.isClassFun
  rw [charInner_indFun _ _ hcl, charInner_indFun _ _ (hcl.comp φ), charInner_indFun _ _ hcl]
  rfl

theorem indFun_mul_comp (φ : H →* G) (ψ : H → ℂ) {χ : G → ℂ} (hχ : IsClassFun χ) :
    indFun φ (ψ * (χ ∘ φ)) = indFun φ ψ * χ := by
  classical
  funext s
  simp only [indFun_apply, Pi.mul_apply, Function.comp_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  split_ifs with hh
  · rw [hh]
    congr 1
    simpa using hχ s t⁻¹
  · simp

omit [Fintype G] [Fintype H] in

theorem IsCharacter.comp {χ : G → ℂ} (hχ : IsCharacter χ) (φ : H →* G) : IsCharacter (χ ∘ φ) := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ.comp φ, rfl⟩

omit [Fintype G] in

theorem IsCharacter.exists_nat_charInner {χ ψ : H → ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    ∃ n : ℕ, charInner H χ ψ = n := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  obtain ⟨W, _, _, _, σ, rfl⟩ := hψ
  exact ⟨_, charInner_character_character σ ρ⟩

theorem IsCharacter.indFun {ψ : H → ℂ} (hψ : IsCharacter ψ) (φ : H →* G) :
    IsCharacter (indFun φ ψ) := by
  rw [isCharacter_iff]
  refine ⟨isClassFun_indFun φ ψ, fun χ hχ ↦ ?_⟩
  have hc := (mem_irrChars.mp hχ).isCharacter
  rw [charInner_indFun φ ψ hc.isClassFun]
  exact hψ.exists_nat_charInner (hc.comp φ)

end IndFun

section IndRep

variable {G H : Type*} [Group G] [Group H] (φ : H →* G)
  {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (ρ : Representation ℂ H A) (σ : Representation ℂ G B)

def indResEquiv : IntertwiningMap (ind φ ρ) σ ≃ₗ[ℂ] IntertwiningMap ρ (σ.comp φ) where
  toFun f := ⟨f.toLinearMap ∘ₗ IndV.mk φ ρ 1, fun h ↦ by
    ext a
    have := IntertwiningMap.isIntertwining _ _ f (φ h) (IndV.mk φ ρ 1 a)
    rw [ind_mk] at this
    change f (IndV.mk φ ρ 1 (ρ h a)) = σ (φ h) (f (IndV.mk φ ρ 1 a))
    rw [← this]
    congr 1
    simp [IndV.mk, ← Coinvariants.mk_inv_tmul, ofMulAction_single]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨Coinvariants.lift _ (TensorProduct.lift <|
      (Finsupp.lift _ _ _ fun g ↦ σ g⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) fun h ↦ by
      have hf : ∀ (h : H) (a : A), f (ρ h a) = σ (φ h) (f a) := fun h a ↦
        IntertwiningMap.isIntertwining _ _ f h a
      ext g a
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, hf], fun g ↦ by
      ext g' a
      simp [mul_inv_rev, map_mul]⟩
  left_inv f := by
    apply IntertwiningMap.ext
    ext g a
    simpa using (IntertwiningMap.isIntertwining _ _ f g⁻¹ (IndV.mk φ ρ 1 a)).symm
  right_inv f := by
    apply IntertwiningMap.ext
    ext a
    simp

variable [Fintype G] [Fintype H] [FiniteDimensional ℂ A]

theorem character_ind : (ind φ ρ).character = indFun φ ρ.character := by
  apply eq_of_isClassFun_of_charInner (isCharacter_character _).isClassFun (isClassFun_indFun _ _)
  intro χ hχ
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := mem_irrChars.mp hχ
  rw [charInner_indFun _ _ (isCharacter_character σ).isClassFun, charInner_comm,
    charInner_character_character, charInner_comm,
    show σ.character ∘ φ = Representation.character (σ.comp φ) from rfl, charInner_character_character,
    (indResEquiv φ ρ σ).finrank_eq]

end IndRep

end GroundTheory.LocalField

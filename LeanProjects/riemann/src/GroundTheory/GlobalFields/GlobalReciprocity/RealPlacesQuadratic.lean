import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.Layers

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract IdeleGroup
open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem eq_of_ker_le_of_natCard_le_two {A B : Type*} [Group A] [Group B] [Finite B]
    (hB : Nat.card B ≤ 2) {f g : A →* B} (hfg : f.ker ≤ g.ker) {y : A} (hy : g y ≠ 1) : f = g := by
  classical
  have key : ∀ b b' : B, b ≠ 1 → b' ≠ 1 → b = b' := by
    intro b b' hb hb'
    by_contra hne
    have : Fintype B := Fintype.ofFinite B
    have h3 : ({1, b, b'} : Finset B).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
      simp [Ne.symm hb, Ne.symm hb']
    have h4 := Finset.card_le_univ ({1, b, b'} : Finset B)
    rw [Nat.card_eq_fintype_card] at hB
    omega
  have hfy : f y ≠ 1 := fun h ↦ hy (hfg h)
  ext x
  by_cases hx : f x = 1
  · rw [hx]
    exact (hfg hx).symm
  · have e : x * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, key _ _ hx hfy, mul_inv_cancel]
    have e' : g x = g y := by
      have h := hfg e
      rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h
    exact key _ _ hx (e' ▸ hy)

theorem abelianization_of_injective {Γ : Type*} [Group Γ] [IsMulCommutative Γ] :
    Function.Injective (Abelianization.of : Γ →* Abelianization Γ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : g ∈ commutator Γ := by
    rw [← Abelianization.ker_of]
    exact hg
  rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (fun x _ y _ ↦ mul_comm' y x)] at h
  exact h

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol _root_.GroundTheory.Global.Cyclotomic

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem exists_eq_ideleClassNorm_of_abstractSymbol_eq_one {c : IdeleClassGroup K.1}
    (h : abstractSymbol K L c = 1) : ∃ d : IdeleClassGroup L.1, FiniteSubfield.ideleClassNorm hKL.out d = c := by
  set e := quotientGaloisEquiv K L
  have key : (Abelianization.map e.symm.toMonoidHom).comp (Abelianization.map e.toMonoidHom) =
      MonoidHom.id _ := by
    refine Abelianization.hom_ext _ _ (MonoidHom.ext fun q ↦ ?_)
    simp
  have hinj : Function.Injective (Abelianization.map e.toMonoidHom) := fun a b hab ↦ by
    have := congrArg (Abelianization.map e.symm.toMonoidHom) hab
    rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, key] at this
  rw [abstractSymbol_apply, ← map_one (Abelianization.map e.toMonoidHom)] at h
  have h1 := hinj h
  rw [MulEquiv.symm_apply_eq, map_one] at h1
  have h2 : fixedEquiv K c ∈ (norm IdeleClassLimit (K.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
      (L.openSubgroup : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).range := by
    rw [normClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(fixedEquiv L).symm b, (fixedEquiv K).injective ?_⟩
  rw [← norm_fixedEquiv hKL.out, MulEquiv.apply_symm_apply]
  exact hb

variable [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem ideleSymbol_eq_one_of_abstractSymbol_eq_one (hL : L.1 ≤ K.1 ⊔ maxCyclotomic)
    {x : IdeleGroup K.1} (h : abstractSymbol K L (IdeleClassGroup.mk K.1 x) = 1) :
    ideleSymbol K.1 L.1 x = 1 := by
  obtain ⟨d, hd⟩ := exists_eq_ideleClassNorm_of_abstractSymbol_eq_one K L h
  obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L.1 d
  have hd' : (QuotientGroup.mk (ideleNorm K.1 L.1 y) : IdeleClassGroup K.1) = QuotientGroup.mk x :=
    hd
  obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hd'
  have hx : x = ideleNorm K.1 L.1 y * diagonal K.1 a := by
    rw [ha, mul_inv_cancel_left]
  rw [hx, map_mul, ideleSymbol_ideleNorm, ideleSymbol_diagonal_eq_one_of_le_sup K L hL, mul_one]

theorem abstractSymbol_mk_of_natCard_le_two (hcard : Nat.card (L.1 ≃ₐ[K.1] L.1) ≤ 2)
    (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) {y : IdeleGroup K.1} (hy : ideleSymbol K.1 L.1 y ≠ 1)
    (x : IdeleGroup K.1) :
    abstractSymbol K L (IdeleClassGroup.mk K.1 x) = Abelianization.of (ideleSymbol K.1 L.1 x) := by
  have hB : Nat.card (Abelianization (L.1 ≃ₐ[K.1] L.1)) ≤ 2 :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective (s := commutator _))).trans hcard
  have h := eq_of_ker_le_of_natCard_le_two hB
    (f := (abstractSymbol K L).comp (IdeleClassGroup.mk K.1))
    (g := Abelianization.of.comp (ideleSymbol K.1 L.1)) (y := y)
    (fun z hz ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        ideleSymbol_eq_one_of_abstractSymbol_eq_one K L hL hz, map_one])
    (fun h1 ↦ hy (abelianization_of_injective (by rw [MonoidHom.comp_apply] at h1; rw [h1, map_one])))
  exact congrArg (fun f : IdeleGroup K.1 →* Abelianization (L.1 ≃ₐ[K.1] L.1) ↦ f x) h

end IdeleClassLimit

end

end GroundTheory.Global

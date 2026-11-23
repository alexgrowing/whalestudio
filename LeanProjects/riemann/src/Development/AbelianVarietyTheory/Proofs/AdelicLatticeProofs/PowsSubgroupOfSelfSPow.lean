import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexTopOfGroupFg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pows_subgroupOf_self_sPow (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    (pows p U).subgroupOf U = pows p (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

theorem pTor_sUnits (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) :
    pTor p (sUnits F S) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmem : ∀ x : Fˣ, x ^ p = 1 → x ∈ sUnits F S := by
    intro x hx
    rw [mem_sUnits]
    intro v _
    have h1 : (v.valuation F (x : F)) ^ p = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx]; simp
    first
      | exact (pow_eq_one_iff hp.ne_zero).mp h1
      | exact (pow_eq_one_iff_left hp.ne_zero).mp h1
      | exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h1
  have e : {x : Fˣ // x ∈ sUnits F S ∧ x ^ p = 1} ≃ rootsOfUnity p F :=
    Equiv.subtypeEquivRight (fun x => by
      rw [mem_rootsOfUnity]; exact ⟨fun h => h.2, fun h => ⟨hmem x h, h⟩⟩)
  rw [pTor, Nat.card_congr e]
  first
    | exact hζ.card_rootsOfUnity
    | (rw [Nat.card_eq_fintype_card]; exact hζ.card_rootsOfUnity)

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

theorem _root_.GlobalTheory.CNorm.pTor_pIdx_sUnits : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    (ζ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
    _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p ∧
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) =
        p ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro p F _ _ ζ S hp hζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := _root_.GlobalTheory.QNorm.sUnits_fg F S
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CNorm.pIdx_top_of_fg p (_root_.GlobalTheory.QNorm.sUnits F S) hp.pos
  have hroots : ∀ x : Fˣ, x ^ p = 1 → x ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    intro x hx
    rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro v _
    have h := congrArg (fun y : Fˣ => HeightOneSpectrum.valuation F v (y : F)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h
  have htor : _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine (Nat.card_congr ?_).trans hζ.card_rootsOfUnity
    exact
      { toFun := fun x => ⟨x.1, (mem_rootsOfUnity p x.1).mpr x.2.2⟩
        invFun := fun y => ⟨y.1, hroots y.1 ((mem_rootsOfUnity p y.1).mp y.2),
          (mem_rootsOfUnity p y.1).mp y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have htorTop : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pTor
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by rw [← Subgroup.coe_pow, x.2.2, OneMemClass.coe_one]⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_top _, Subtype.ext y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hidxTop : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by rw [← hy]; rfl⟩
    · rintro ⟨y, hyH, hy⟩
      exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩
  refine ⟨htor, ?_⟩
  rw [← hidxTop, h2, htorTop, htor, ← _root_.GlobalTheory.QNorm.sUnits_rank F S, pow_succ]

end GlobalTheory.CNorm

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Klm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hn : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ i : ℕ, i.Coprime M ∧ s ζ = ζ ^ i ∧
      (i : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hcard : Nat.card (rootsOfUnity M Ω) = M := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω M
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  set c := modularCyclotomicCharacter Ω hcard s.toRingEquiv with hc
  have hsζ : s ζ = ζ ^ (c : ZMod M).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard s.toRingEquiv hζ.toRootsOfUnity.2
    simpa using h
  refine ⟨ζ, hζ, (c : ZMod M).val, ZMod.val_coe_unit_coprime c, hsζ, ?_⟩
  rw [cyclotomicCharacter.toZModPow]
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hcard' : Nat.card (rootsOfUnity (l ^ n) Ω) = l ^ n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)
  set c' := modularCyclotomicCharacter Ω hcard' s.toRingEquiv
  have hζ' : IsPrimitiveRoot (ζ ^ (M / l ^ n)) (l ^ n) :=
    hζ.pow hM (Nat.div_mul_cancel hn).symm
  have h1 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c : ZMod M).val := by
    rw [map_pow, hsζ, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c' : ZMod (l ^ n)).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard' s.toRingEquiv hζ'.toRootsOfUnity.2
    simpa using h
  have hfin : IsOfFinOrder (ζ ^ (M / l ^ n)) :=
    orderOf_pos_iff.1 (by rw [← hζ'.eq_orderOf]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h3 := hfin.pow_eq_pow_iff_modEq.1 (h1.symm.trans h2)
  rw [← hζ'.eq_orderOf] at h3
  rw [← ZMod.natCast_zmod_val (c' : ZMod (l ^ n))]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.exists_sl2_conj_diag_zmod (M i : ℕ) (hi : i.Coprime M) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), (_root_.GlobalTheory.KZ.en γ 0 0 : ZMod M) = _root_.GlobalTheory.KZ.en δ 0 0 ∧
      (_root_.GlobalTheory.KZ.en γ 0 1 : ZMod M) = (i : ZMod M) * _root_.GlobalTheory.KZ.en δ 0 1 ∧
      (i : ZMod M) * _root_.GlobalTheory.KZ.en γ 1 0 = _root_.GlobalTheory.KZ.en δ 1 0 ∧
      (_root_.GlobalTheory.KZ.en γ 1 1 : ZMod M) = _root_.GlobalTheory.KZ.en δ 1 1 := by
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime i hi
  have hu : (u : ZMod M) = i := rfl
  have hγdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hγdet
  set m : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod M),
      ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M);
      (i : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M),
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M)] with hm_def
  have hm : m.det = 1 := by
    rw [hm_def, Matrix.det_fin_two_of]
    have h1 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (i : ZMod M) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (Int.cast : ℤ → ZMod M) hγdet
    push_cast at h2
    linear_combination h2 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M) * h1
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M ⟨m, hm⟩
  have he : ∀ a b, (((δ : Matrix (Fin 2) (Fin 2) ℤ) a b : ℤ) : ZMod M) = m a b := fun a b => by
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) a b) hδ
    simpa using h
  refine ⟨δ, ?_, ?_, ?_, ?_⟩ <;> simp only [_root_.GlobalTheory.KZ.en, he, hm_def]
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
  · simp
  · simp

theorem exists_conj_level_exponent :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M →
      l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧
      ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧
        (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧
        (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  intro Ω _ _ _ N l n M _ hM hN hl hn s γ hγ
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hn s
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_sl2_conj_diag_zmod M i hi γ
  have red : ∀ {K : ℕ}, K ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod K) = y := fun {K} hK x y h => by
    simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h
  have h10' : (((i : ℤ) * en γ 1 0 : ℤ) : ZMod M) = en δ 1 0 := by push_cast; exact h10
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ1
  have a4 := CongruenceSubgroup.Gamma0_mem.1 hγ0
  refine ⟨δ, Subgroup.mem_inf.2 ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨?_, ?_, ?_⟩,
    CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ζ, hζ, i, by rw [zpow_natCast, hs], ⟨h00, ?_, ?_, h11⟩, ?_⟩
  · exact (red hN h00).symm.trans a1
  · exact (red hN h11).symm.trans a2
  · refine (red hN h10').symm.trans ?_
    have : (en γ 1 0 : ZMod N) = 0 := a3
    rw [Int.cast_mul, this, mul_zero]
  · refine (red hl h10').symm.trans ?_
    have : (en γ 1 0 : ZMod l) = 0 := a4
    rw [Int.cast_mul, this, mul_zero]
  · simpa only [Int.cast_natCast] using h01
  · simpa only [Int.cast_natCast] using h10
  · simpa only [Int.cast_natCast] using hχ

end GlobalTheory

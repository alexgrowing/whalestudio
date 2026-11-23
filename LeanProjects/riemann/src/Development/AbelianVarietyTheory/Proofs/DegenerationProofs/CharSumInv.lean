import Mathlib

namespace GlobalTheory.CharacterSumInverse

open scoped BigOperators

theorem charSum_inv {o : Type} [CommRing o] [IsDomain o] {T : Type} [CommGroup T] [Fintype T]
    [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)] [DecidableEq T] (t : T) :
    (∑ c : T →* oˣ, ((c t)⁻¹ : oˣ).val) = if t = 1 then (Fintype.card T : o) else 0 := by
  classical
  have hinv : ∀ c : T →* oˣ, ((c t)⁻¹ : oˣ).val = (c t⁻¹).val := fun c => by rw [map_inv]
  simp_rw [hinv]
  split_ifs with ht
  · subst ht
    simp only [inv_one, map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    have h := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T o
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [h]
  · have hs : t⁻¹ ≠ 1 := by simpa using ht
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity T o hs
    set S := ∑ c : T →* oˣ, (c t⁻¹).val with hS
    have hshift : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = S :=
      Fintype.sum_equiv (Equiv.mulLeft φ) _ _ (fun _ => rfl)
    have hmul : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = (φ t⁻¹).val * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp [MonoidHom.mul_apply, Units.val_mul]
    have h0 : ((φ t⁻¹).val - 1) * S = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    have hne : (φ t⁻¹).val - 1 ≠ 0 := by
      intro h
      apply hφ
      exact Units.val_eq_one.mp (sub_eq_zero.mp h)
    exact (mul_eq_zero.mp h0).resolve_left hne

theorem main : (let d1 : {o : Type} → [inst : CommRing o] → {T : Type} → [inst_1 : CommGroup T] → {M : Type} → [inst_2 : AddCommGroup M] → [inst_3 : Module o M] → [Fintype T] → Representation o T M → o → (T →* oˣ) → M →ₗ[o] M := @(fun {o : Type} [CommRing o] {T : Type} [CommGroup T] {M : Type} [AddCommGroup M] [Module o M] [Fintype T] (ρ : Representation o T M) (u : o) (c : T →* oˣ) ↦ u • ∑ t : T, (↑((c : T → oˣ) t)⁻¹ : o) • (ρ : T → M →ₗ[o] M) t); ∀ {o : Type} [inst : CommRing o] {T : Type} [inst_1 : CommGroup T] {M : Type} [inst_2 : AddCommGroup M] [inst_3 : Module o M] [inst_4 : Fintype T] (ρ : Representation o T M) (u : o) [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [inst_7 : Fintype (T →* oˣ)], u * (↑(Fintype.card T) : o) = (1 : o) → ∀ (x : M), ∑ c : T →* oˣ, (d1 ρ u c : M → M) x = x) := by
  intro d1 o _ T _ M _ _ _ ρ u _ _ _ hu x
  classical
  simp only [d1, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, charSum_inv]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one,
    Module.End.one_apply]
  rw [smul_smul, hu, one_smul]

end GlobalTheory.CharacterSumInverse

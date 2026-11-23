import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountGen

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section split

variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))

theorem ffH_fst' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).1 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).1 * (x l).1 := by
  simp only [ffH, Prod.fst_sum, Prod.fst_mul]

theorem ffH_snd' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).2 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).2 * (x l).2 := by
  simp only [ffH, Prod.snd_sum, Prod.snd_mul]

theorem ffH_self_of_snd (x : Fin M → k × k) (h : ∀ l, (x l).2 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

theorem ffH_self_of_fst (x : Fin M → k × k) (h : ∀ l, (x l).1 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

theorem notFree_iff (x : Fin M → k × k) :
    (¬ ∀ c : k × k, c • x = 0 → c = 0) ↔ (∀ l, (x l).1 = 0) ∨ (∀ l, (x l).2 = 0) := by
  constructor
  · intro h
    push_neg at h
    obtain ⟨c, hc, hne⟩ := h
    by_cases h1 : c.1 = 0
    · right
      have h2 : c.2 ≠ 0 := fun h2 => hne (Prod.ext h1 h2)
      intro l
      have hl := congrArg Prod.snd (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul, Pi.zero_apply, Prod.snd_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h2
    · left
      intro l
      have hl := congrArg Prod.fst (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.zero_apply, Prod.fst_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h1
  · rintro (h | h) hfree
    · have h1 := hfree (1, 0) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1
    · have h1 := hfree (0, 1) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1

theorem perp_surj {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) (w : Fin a' → k × k) :
    ∃ x : Fin M → k × k, ∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = w j := by
  classical
  set c := T0⁻¹.mulVec w with hc
  refine ⟨fun l => ∑ m, Y m l * c m, fun j => ?_⟩

  have h1 : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j)
      (fun l => ∑ m, Y m l * c m) = ∑ m, T0 j m * c m := by
    rw [← hY]
    simp only [ffGram, ffH, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h1]
  have h2 : T0.mulVec c = w := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h3 := congrFun h2 j
  simpa [Matrix.mulVec, dotProduct] using h3

private theorem natCard_ker_mul_card_pow_eq_of_surjective [Finite k] {a' : ℕ} (B : Matrix (Fin a') (Fin M) k)
    (hB : Function.Surjective B.mulVec) :
    Nat.card {u : Fin M → k // B.mulVec u = 0} * Nat.card k ^ a' = Nat.card k ^ M := by
  classical
  have _ := Fintype.ofFinite k
  have hs : LinearMap.range (Matrix.mulVecLin B) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨u, hu⟩ := hB v
    exact ⟨u, by rw [Matrix.mulVecLin_apply, hu]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  have e : {u : Fin M → k // B.mulVec u = 0} ≃ LinearMap.ker (Matrix.mulVecLin B) :=
    Equiv.subtypeEquivRight fun u => by simp [Matrix.mulVecLin_apply]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (Matrix.mulVecLin B)), ← pow_add]
  congr 1
  omega

theorem card_half_snd [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).1
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).1 =
        B.mulVec (fun l => (x l).1) j := by
    intro x j
    rw [ffH_fst']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (w' j, 0))
    exact ⟨fun l => (x l).1, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).1, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (u.1 l, 0), fun j => by
        refine Prod.ext ?_ ?_
        · rw [hB]
          exact congrFun u.2 j
        · rw [ffH_snd']
          simp, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext rfl (x.2.2 l).symm)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

theorem card_half_fst [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).2
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).2 =
        B.mulVec (fun l => (x l).2) j := by
    intro x j
    rw [ffH_snd']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (0, w' j))
    exact ⟨fun l => (x l).2, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).2, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (0, u.1 l), fun j => by
        refine Prod.ext ?_ ?_
        · rw [ffH_fst']
          simp
        · rw [hB]
          exact congrFun u.2 j, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext (x.2.2 l).symm rfl)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

end split

end PI.OmVe

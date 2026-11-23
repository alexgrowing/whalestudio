import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing

open Matrix GlobalTheory.SUCong

namespace GlobalTheory.SkewCount

theorem card_ker_linear {K : Type} [CommRing K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (γ : ι → K) (p : ι) (hp : IsUnit (γ p)) :
    Nat.card {a : ι → K // ∑ i, a i * γ i = 0} = Nat.card K ^ (Fintype.card ι - 1) := by
  obtain ⟨v, hv⟩ := hp.exists_right_inv
  have hs : ∀ a : ι → K, ∑ i, a i * γ i = a p * γ p + ∑ i : {i // i ≠ p}, a i * γ i :=
    fun a => Fintype.sum_eq_add_sum_subtype_ne _ p
  let ext : ({i // i ≠ p} → K) → ι → K := fun b i =>
    if h : i = p then -(∑ j : {j // j ≠ p}, b j * γ j) * v else b ⟨i, h⟩
  have hext_ne : ∀ b (j : {j // j ≠ p}), ext b j = b j := fun b j => by
    simp only [ext, dif_neg j.2]
  have hext_p : ∀ b, ext b p = -(∑ j : {j // j ≠ p}, b j * γ j) * v := fun b => by
    simp only [ext, dif_pos rfl]
  let e : {a : ι → K // ∑ i, a i * γ i = 0} ≃ ({i // i ≠ p} → K) :=
    { toFun := fun a i => a.1 i
      invFun := fun b => ⟨ext b, by
        rw [hs, hext_p]
        simp only [hext_ne]
        linear_combination (-(∑ j : {j // j ≠ p}, b j * γ j)) * hv⟩
      left_inv := fun a => by
        apply Subtype.ext
        funext i
        by_cases h : i = p
        · subst h
          simp only
          rw [hext_p]
          have h0 := a.2
          rw [hs] at h0
          linear_combination (-v) * h0 + a.1 i * hv
        · exact hext_ne (fun j => a.1 j) ⟨i, h⟩
      right_inv := fun b => by
        funext j
        exact hext_ne b j }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := {i // i ≠ p}),
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]

section Ring

variable {R : Type} [CommRing R]

def bet (τ : R →+* R) (v x : R) : R := (x - τ x) * v

def alp (τ : R →+* R) (v w x : R) : R := x - bet τ v x * w

variable (τ : R →+* R) (k : Subring R) (w v : R)

theorem bet_dec (hk : ∀ x ∈ k, τ x = x) (hv : (w - τ w) * v = 1) {a b : R} (ha : a ∈ k)
    (hb : b ∈ k) : bet τ v (a + b * w) = b := by
  simp only [bet, map_add, map_mul, hk a ha, hk b hb]
  linear_combination b * hv

theorem alp_dec (hk : ∀ x ∈ k, τ x = x) (hv : (w - τ w) * v = 1) {a b : R} (ha : a ∈ k)
    (hb : b ∈ k) : alp τ v w (a + b * w) = a := by
  simp only [alp, bet_dec τ k w v hk hv ha hb]
  ring

theorem bet_mem (hk : ∀ x ∈ k, τ x = x) (hv : (w - τ w) * v = 1)
    (hdec : ∀ x : R, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) (x : R) : bet τ v x ∈ k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
  rwa [bet_dec τ k w v hk hv ha hb]

theorem alp_mem (hk : ∀ x ∈ k, τ x = x) (hv : (w - τ w) * v = 1)
    (hdec : ∀ x : R, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) (x : R) : alp τ v w x ∈ k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
  rwa [alp_dec τ k w v hk hv ha hb]

theorem skew_entry (hw : w + τ w = 1) (hv : (w - τ w) * v = 1) {x y : R} (hx : τ x = -y)
    (hy : τ y = -x) : x = alp τ v w x * (1 - w) - alp τ v w y * w := by
  have h1 : τ w = 1 - w := by linear_combination hw
  rw [h1] at hv
  simp only [alp, bet, hx, hy]
  linear_combination (-(x + y) * w) * hv

end Ring

section Main

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_apply (τ : R →+* R) (M : Matrix n n R) (i j : n) : Formalism.UG.cT τ M i j = τ (M j i) := rfl

def leftEquiv (τ : R →+* R) (Hb H' : Matrix n n R) (hHb : Formalism.UG.cT τ Hb = Hb) (hinv : Hb * H' = 1) :
    {Y : Matrix n n R // Formalism.UG.cT τ Y * Hb + Hb * Y = 0 ∧ Y.trace = 0} ≃
      {Z : Matrix n n R // Formalism.UG.cT τ Z = -Z ∧ (H' * Z).trace = 0} :=
  have h' : H' * Hb = 1 := _root_.mul_eq_one_comm.mp hinv
  Equiv.subtypeEquiv
    { toFun := fun Y => Hb * Y
      invFun := fun Z => H' * Z
      left_inv := fun Y => by simp only [← Matrix.mul_assoc, h', Matrix.one_mul]
      right_inv := fun Z => by simp only [← Matrix.mul_assoc, hinv, Matrix.one_mul] }
    (fun Y => by
      simp only [Equiv.coe_fn_mk, Formalism.UG.cT_mul, hHb, ← Matrix.mul_assoc, h', Matrix.one_mul]
      rw [eq_neg_iff_add_eq_zero])

end Main

section Skew

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
variable (τ : R →+* R) (k : Subring R) (w v : R)

def skewEquiv (hk : ∀ x ∈ k, τ x = x) (hw : w + τ w = 1) (hv : (w - τ w) * v = 1)
    (hdec : ∀ x : R, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) :
    {Z : Matrix n n R // Formalism.UG.cT τ Z = -Z} ≃ (n × n → k) where
  toFun Z p := ⟨alp τ v w (Z.1 p.1 p.2), alp_mem τ k w v hk hv hdec _⟩
  invFun f := ⟨Matrix.of fun i j => (f (i, j) : R) * (1 - w) - (f (j, i) : R) * w, by
    have h1 : τ w = 1 - w := by linear_combination hw
    ext i j
    show τ ((f (j, i) : R) * (1 - w) - (f (i, j) : R) * w) =
      -((f (i, j) : R) * (1 - w) - (f (j, i) : R) * w)
    simp only [map_sub, map_mul, hk _ (f _).2, map_one, h1]
    ring⟩
  left_inv Z := by
    apply Subtype.ext
    funext i j
    have hx : τ (Z.1 i j) = -(Z.1 j i) := by
      have := congrFun (congrFun Z.2 j) i
      rwa [cT_apply, Matrix.neg_apply] at this
    have hy : τ (Z.1 j i) = -(Z.1 i j) := by
      have := congrFun (congrFun Z.2 i) j
      rwa [cT_apply, Matrix.neg_apply] at this
    exact (skew_entry τ w v hw hv hx hy).symm
  right_inv f := by
    funext p
    apply Subtype.ext
    show alp τ v w ((f (p.1, p.2) : R) * (1 - w) - (f (p.2, p.1) : R) * w) = f p
    have e : (f (p.1, p.2) : R) * (1 - w) - (f (p.2, p.1) : R) * w =
        (f p : R) + (-((f p : R) + (f (p.2, p.1) : R))) * w := by ring
    rw [e, alp_dec τ k w v hk hv (f p).2 (neg_mem (add_mem (f p).2 (f _).2))]

theorem trace_coord (hk : ∀ x ∈ k, τ x = x) (hw : w + τ w = 1) (H' : Matrix n n R)
    (hH' : ∀ i j, τ (H' j i) = H' i j) (f : n × n → k) (γ : n × n → k)
    (hγ : ∀ p, (γ p : R) = bet τ v (H' p.2 p.1 * (1 - w))) :
    (∑ p, (f p : R) * (γ p : R)) =
      (∑ a, ∑ b, H' a b * ((f (b, a) : R) * (1 - w) - (f (a, b) : R) * w)) * v := by
  have h1 : τ w = 1 - w := by linear_combination hw
  have hg : ∀ a b, (γ (a, b) : R) = (H' b a * (1 - w) - H' a b * w) * v := fun a b => by
    rw [hγ, bet]
    simp only [map_mul, map_sub, map_one, h1, hH']
    ring
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [hg]
  have e1 : ∀ a, ∑ b, (f (a, b) : R) * ((H' b a * (1 - w) - H' a b * w) * v) =
      ∑ b, (f (a, b) : R) * H' b a * (1 - w) * v - ∑ b, (f (a, b) : R) * H' a b * w * v := by
    intro a
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∀ a, (∑ b, H' a b * ((f (b, a) : R) * (1 - w) - (f (a, b) : R) * w)) * v =
      ∑ b, (f (b, a) : R) * H' a b * (1 - w) * v - ∑ b, (f (a, b) : R) * H' a b * w * v := by
    intro a
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [e1, e2, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => (f (a, b) : R) * H' b a * (1 - w) * v)]

end Skew

theorem card_skew_traceless :
    ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (τ : R →+* R) (k : Subring R)
      (w : R) (Hb H' : Matrix n n R) (q : ℕ), (∀ x ∈ k, τ x = x) → w + τ w = 1 →
      IsUnit (w - τ w) → (∀ x : R, ∃ a ∈ k, ∃ b ∈ k, x = a + b * w) →
      (∀ x ∈ k, x ≠ 0 → ∃ y ∈ k, x * y = 1) → Nat.card k = q → Formalism.UG.cT τ Hb = Hb →
      Hb * H' = 1 →
      Nat.card {Y : Matrix n n R // Formalism.UG.cT τ Y * Hb + Hb * Y = 0 ∧ Y.trace = 0} =
        q ^ (Fintype.card n ^ 2 - 1) := by
  intro R _ n _ _ τ k w Hb H' q hk hw hu hdec hfield hq hHb hinv
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : τ w = 1 - w := by linear_combination hw
  have hcT : Formalism.UG.cT τ H' = H' := by
    have h2 : Formalism.UG.cT τ H' * Hb = 1 := by
      have := congrArg (Formalism.UG.cT τ) hinv
      rwa [Formalism.UG.cT_mul, Formalism.UG.cT_one, hHb] at this
    calc Formalism.UG.cT τ H' = Formalism.UG.cT τ H' * (Hb * H') := by rw [hinv, Matrix.mul_one]
      _ = H' := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH' : ∀ i j, τ (H' j i) = H' i j := fun i j => congrFun (congrFun hcT i) j
  have hbm := bet_mem τ k w v hk hv hdec
  let γ : n × n → k := fun p => ⟨bet τ v (H' p.2 p.1 * (1 - w)), hbm _⟩
  by_cases hex : ∃ p, γ p ≠ 0
  · obtain ⟨p, hp⟩ := hex
    have hunit : IsUnit (γ p) := by
      obtain ⟨y, hy, hxy⟩ := hfield (γ p) (γ p).2 (fun h => hp (Subtype.ext h))
      exact ⟨⟨γ p, ⟨y, hy⟩, Subtype.ext hxy, by rw [mul_comm]; exact Subtype.ext hxy⟩, rfl⟩
    have cond : ∀ f : n × n → k,
        (H' * ((skewEquiv τ k w v hk hw hv hdec (n := n)).symm f).1).trace = 0 ↔
          ∑ p, f p * γ p = 0 := by
      intro f
      have hs := trace_coord τ k w v hk hw H' hH' f γ (fun _ => rfl)
      have ht : (H' * ((skewEquiv τ k w v hk hw hv hdec (n := n)).symm f).1).trace =
          ∑ a, ∑ b, H' a b * ((f (b, a) : R) * (1 - w) - (f (a, b) : R) * w) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        rfl
      rw [ht, ← Subtype.coe_inj, ZeroMemClass.coe_zero]
      push_cast
      rw [hs]
      constructor
      · intro h; rw [h, zero_mul]
      · intro h
        linear_combination (w - τ w) * h - (∑ a, ∑ b, H' a b *
          ((f (b, a) : R) * (1 - w) - (f (a, b) : R) * w)) * hv
    let E := (leftEquiv τ Hb H' hHb hinv).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter (fun Z : Matrix n n R => Formalism.UG.cT τ Z = -Z)
          (fun Z => (H' * Z).trace = 0)).symm.trans
        (Equiv.subtypeEquiv (q := fun f : n × n → k => ∑ p, f p * γ p = 0)
          (skewEquiv τ k w v hk hw hv hdec) (fun Z => by
          have := cond (skewEquiv τ k w v hk hw hv hdec Z)
          rwa [Equiv.symm_apply_apply] at this)))
    rw [Nat.card_congr E, card_ker_linear γ p hunit, hq, Fintype.card_prod, sq]
  · push_neg at hex
    have hz : ∀ i j, H' i j = 0 := by
      have E : ∀ i j, H' i j * (1 - w) - H' j i * w = 0 := by
        intro i j
        have h0 : bet τ v (H' i j * (1 - w)) = 0 := congrArg Subtype.val (hex (j, i))
        rw [bet] at h0
        simp only [map_mul, map_sub, map_one, h1, hH'] at h0
        linear_combination (w - τ w) * h0 - (H' i j * (1 - w) - H' j i * w) * hv
      intro i j
      rw [h1] at hv
      linear_combination (-H' i j) * hv - v * (1 - w) * E i j - v * w * E j i
    have h0 : H' = 0 := Matrix.ext hz
    have hsub : Subsingleton (Matrix n n R) := by
      by_cases hn : IsEmpty n
      · exact ⟨fun A B => Matrix.ext fun i => isEmptyElim i⟩
      · obtain ⟨i⟩ := not_isEmpty_iff.mp hn
        have h10 : (1 : R) = 0 := by
          have := congrFun (congrFun hinv i) i
          rw [h0, Matrix.mul_zero, Matrix.one_apply_eq] at this
          exact this.symm
        haveI : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
        exact ⟨fun A B => Matrix.ext fun _ _ => Subsingleton.elim _ _⟩
    rw [Nat.card_of_subsingleton (⟨0, by simp [Formalism.UG.cT]⟩ :
      {Y : Matrix n n R // Formalism.UG.cT τ Y * Hb + Hb * Y = 0 ∧ Y.trace = 0})]
    by_cases hn : IsEmpty n
    · rw [Fintype.card_eq_zero]; simp
    · obtain ⟨i⟩ := not_isEmpty_iff.mp hn
      have h10 : (1 : R) = 0 := by
        have := congrFun (congrFun hinv i) i
        rw [h0, Matrix.mul_zero, Matrix.one_apply_eq] at this
        exact this.symm
      haveI : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
      haveI : Subsingleton k := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [← hq, Nat.card_of_subsingleton (0 : k), one_pow]

end GlobalTheory.SkewCount

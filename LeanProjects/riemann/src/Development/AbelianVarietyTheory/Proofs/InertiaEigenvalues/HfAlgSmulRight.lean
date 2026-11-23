import Mathlib

open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

def hf (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) : K :=
  (fun i => cK (x i)) ⬝ᵥ (J.mulVec y)

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_add_right (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (y + z) =
      _root_.GlobalTheory.HermNbr.hf cK J x y + _root_.GlobalTheory.HermNbr.hf cK J x z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, Matrix.mulVec_add, dotProduct, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_add_left (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (x + y) z =
      _root_.GlobalTheory.HermNbr.hf cK J x z + _root_.GlobalTheory.HermNbr.hf cK J y z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_smul_right (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : K) (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (a • y) = a * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_algSmul_right (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : O)
    (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (a • y) =
      algebraMap O K a * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  rw [← algebraMap_smul K a y, _root_.GlobalTheory.HermNbr.hf_smul_right]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_algSmul_left (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : O)
    (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (a • x) y =
      cK (algebraMap O K a) * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.smul_apply, Algebra.smul_def,
    map_mul, Finset.mul_sum, mul_assoc]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_sub_right (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (y - z) =
      _root_.GlobalTheory.HermNbr.hf cK J x y - _root_.GlobalTheory.HermNbr.hf cK J x z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, Matrix.mulVec_sub, dotProduct, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_sub_left (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (x - y) z =
      _root_.GlobalTheory.HermNbr.hf cK J x z - _root_.GlobalTheory.HermNbr.hf cK J y z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.sub_apply, map_sub, sub_mul,
    Finset.sum_sub_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in

theorem _root_.GlobalTheory.HermNbr.hf_conj (cK : K ≃+* K) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) K)
    (hJ : J.transpose.map cK = J) (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J y x = cK (_root_.GlobalTheory.HermNbr.hf cK J x y) := by
  have hJ' : ∀ i j, cK (J i j) = J j i := fun i j => by
    simpa using congrFun (congrFun hJ j) i
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Matrix.mulVec, map_sum, map_mul, hc2,
    hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def perp (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K))
    (v : Fin r → K) : Submodule O (Fin r → K) where
  carrier := {x | x ∈ L ∧ hf cK J v x ∈ (algebraMap O K).range}
  add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, by
    rw [hf_add_right]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨L.zero_mem, by
    have := hf_smul_right cK J 0 v 0
    simp only [zero_smul, zero_mul] at this
    rw [this]; exact zero_mem _⟩
  smul_mem' := fun a x hx => ⟨L.smul_mem a hx.1, by
    rw [hf_algSmul_right]; exact mul_mem ⟨a, rfl⟩ hx.2⟩

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.mem_perp {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K}
    {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ _root_.GlobalTheory.HermNbr.perp cK J L v ↔
      x ∈ L ∧ _root_.GlobalTheory.HermNbr.hf cK J v x ∈ (algebraMap O K).range :=
  Iff.rfl

def nb (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K))
    (v : Fin r → K) : Submodule O (Fin r → K) :=
  perp cK J L v ⊔ Submodule.span O {v}

def IsSD (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, hf cK J x y ∈ (algebraMap O K).range

noncomputable def idx (ϖ : O) (L : Submodule O (Fin r → K)) : ℕ :=
  (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.relIndex
    L.toAddSubgroup

def Good (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O) (N : ℕ)
    (L : Submodule O (Fin r → K)) : Prop :=
  IsSD cK J L ∧ (∀ x : Fin r → K, ∃ k : ℕ, (ϖ ^ k) • x ∈ L) ∧ idx ϖ L = N

def IsStep (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O)
    (L : Submodule O (Fin r → K)) (v : Fin r → K) : Prop :=
  v ∉ L ∧ ϖ • v ∈ L ∧ hf cK J v v ∈ (algebraMap O K).range

def Nbrs (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O)
    (L : Submodule O (Fin r → K)) : Set (Submodule O (Fin r → K)) :=
  {L' | ∃ v, IsStep cK J ϖ L v ∧ L' = nb cK J L v}

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in

theorem _root_.GlobalTheory.HermNbr.graph_sum {X : Type} (S : Set X) (i : X → X → ℕ)
    (Nb : X → Set X) (Q : ℕ) (hQ : 2 ≤ Q)
    (s D : ℝ) (hs : 0 < s) (hD : 0 ≤ D)
    (hρ : D * (Q : ℝ) ^ (-s) < 1)
    (hself : ∀ L ∈ S, i L L = 1)
    (hstep : ∀ L ∈ S, ∀ Λ ∈ S, L ≠ Λ → i L Λ ≠ 0 →
      ∃ L' ∈ Nb L, L' ∈ S ∧ i L' Λ ≠ 0 ∧ Q * i L' Λ ≤ i L Λ)
    (hcard : ∀ L ∈ S, ∀ t : Finset X, (t : Set X) ⊆ Nb L → (t.card : ℝ) ≤ D)
    (L : X) (hL : L ∈ S) (C : Finset X) (hC : (C : Set X) ⊆ S) (hLC : L ∉ C) :
    ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) ≤
      D * (Q : ℝ) ^ (-s) / (1 - D * (Q : ℝ) ^ (-s)) := by
  classical
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hq0 : 0 ≤ (Q : ℝ) ^ (-s) := Real.rpow_nonneg hQpos.le _
  generalize hq : (Q : ℝ) ^ (-s) = q at hρ hq0 ⊢
  obtain ⟨B, hBdef⟩ : ∃ B, B = D * q / (1 - D * q) := ⟨_, rfl⟩
  rw [← hBdef]
  have hne : (1 - D * q) ≠ 0 := (sub_pos.2 hρ).ne'
  have hB : 0 ≤ B := hBdef ▸ div_nonneg (mul_nonneg hD hq0) (sub_pos.2 hρ).le
  have hfix : D * q * (1 + B) = B := by
    rw [hBdef, one_add_div hne, sub_add_cancel, mul_div_assoc', mul_one]
  have hzero : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (neg_ne_zero.2 hs.ne')
  have main : ∀ n : ℕ, ∀ L ∈ S, ∀ C : Finset X, (C : Set X) ⊆ S → L ∉ C →
      (∀ Λ ∈ C, i L Λ ≤ n) → ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) ≤ B := by
    intro n
    induction n with
    | zero =>
      intro L hL C hC hLC hn
      have h0 : ∀ Λ ∈ C, (i L Λ : ℝ) ^ (-s) = 0 := fun Λ hΛ => by
        rw [Nat.le_zero.1 (hn Λ hΛ), Nat.cast_zero, hzero]
      rw [Finset.sum_eq_zero h0]
      exact hB
    | succ n ih =>
      intro L hL C hC hLC hn
      have key : ∀ Λ, ∃ L', Λ ∈ S → L ≠ Λ → i L Λ ≠ 0 →
          L' ∈ Nb L ∧ L' ∈ S ∧ i L' Λ ≠ 0 ∧ Q * i L' Λ ≤ i L Λ := by
        intro Λ
        by_cases h : Λ ∈ S ∧ L ≠ Λ ∧ i L Λ ≠ 0
        · obtain ⟨L', h1, h2, h3, h4⟩ := hstep L hL Λ h.1 h.2.1 h.2.2
          exact ⟨L', fun _ _ _ => ⟨h1, h2, h3, h4⟩⟩
        · exact ⟨L, fun a b c => absurd ⟨a, b, c⟩ h⟩
      choose f hf using key
      obtain ⟨C', hC'⟩ : ∃ C', C' = C.filter (fun Λ => i L Λ ≠ 0) := ⟨_, rfl⟩
      have hC'C : C' ⊆ C := hC' ▸ Finset.filter_subset _ _
      have hf' : ∀ Λ ∈ C', f Λ ∈ Nb L ∧ f Λ ∈ S ∧ i (f Λ) Λ ≠ 0 ∧ Q * i (f Λ) Λ ≤ i L Λ := by
        intro Λ hΛ
        rw [hC', Finset.mem_filter] at hΛ
        exact hf Λ (hC hΛ.1) (fun h => hLC (by rw [h]; exact hΛ.1)) hΛ.2
      have hsum : ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) = ∑ Λ ∈ C', (i L Λ : ℝ) ^ (-s) := by
        rw [hC', Finset.sum_filter_of_ne]
        intro Λ _ h h0
        exact h (by rw [h0, Nat.cast_zero, hzero])
      have fibre : ∀ L1 ∈ S, ∀ Fb : Finset X, (∀ Λ ∈ Fb, Λ ∈ C' ∧ f Λ = L1) →
          ∑ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ q * (1 + B) := by
        intro L1 hL1 Fb hFb
        have hterm : ∀ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ q * (i L1 Λ : ℝ) ^ (-s) := by
          intro Λ hΛ
          obtain ⟨hΛC', hfΛ⟩ := hFb Λ hΛ
          obtain ⟨-, -, hne', hle⟩ := hf' Λ hΛC'
          rw [hfΛ] at hne' hle
          have h1 : (1 : ℝ) ≤ i L1 Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne'
          have h2 : (Q : ℝ) * i L1 Λ ≤ i L Λ := by exact_mod_cast hle
          have h3 : 0 < (Q : ℝ) * i L1 Λ := mul_pos hQpos (by linarith)
          rw [← hq, ← Real.mul_rpow hQpos.le (by linarith), Real.rpow_neg (Nat.cast_nonneg _),
            Real.rpow_neg h3.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos h3 _) (Real.rpow_le_rpow h3.le h2 hs.le)
        have hIH : ∑ Λ ∈ Fb.erase L1, (i L1 Λ : ℝ) ^ (-s) ≤ B := by
          refine ih L1 hL1 (Fb.erase L1) ?_ (Finset.notMem_erase L1 Fb) ?_
          · intro x hx
            exact hC (hC'C (hFb x (Finset.mem_of_mem_erase hx)).1)
          · intro Λ hΛ
            obtain ⟨hΛC', hfΛ⟩ := hFb Λ (Finset.mem_of_mem_erase hΛ)
            obtain ⟨-, -, hne', hle⟩ := hf' Λ hΛC'
            rw [hfΛ] at hne' hle
            have h1 := hn Λ (hC'C hΛC')
            have h2 : 1 ≤ i L1 Λ := Nat.one_le_iff_ne_zero.2 hne'
            have h3 : 2 * i L1 Λ ≤ Q * i L1 Λ := Nat.mul_le_mul_right _ hQ
            omega
        calc ∑ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ ∑ Λ ∈ Fb, q * (i L1 Λ : ℝ) ^ (-s) :=
              Finset.sum_le_sum hterm
          _ = q * ∑ Λ ∈ Fb, (i L1 Λ : ℝ) ^ (-s) := by rw [Finset.mul_sum]
          _ ≤ q * ∑ Λ ∈ insert L1 (Fb.erase L1), (i L1 Λ : ℝ) ^ (-s) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_insert_iff.2 subset_rfl)
                (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) hq0
          _ = q * (1 + ∑ Λ ∈ Fb.erase L1, (i L1 Λ : ℝ) ^ (-s)) := by
              rw [Finset.sum_insert (Finset.notMem_erase L1 Fb), hself L1 hL1, Nat.cast_one,
                Real.one_rpow]
          _ ≤ q * (1 + B) := mul_le_mul_of_nonneg_left (by linarith) hq0
      rw [hsum, ← Finset.sum_fiberwise_of_maps_to (g := f) (t := C'.image f)
        (fun Λ hΛ => Finset.mem_image_of_mem f hΛ)]
      calc _ ≤ ∑ _L' ∈ C'.image f, q * (1 + B) := by
            refine Finset.sum_le_sum fun L' hL' => ?_
            obtain ⟨Λ0, hΛ0, rfl⟩ := Finset.mem_image.1 hL'
            exact fibre _ (hf' Λ0 hΛ0).2.1 _ fun Λ hΛ => Finset.mem_filter.1 hΛ
        _ = ((C'.image f).card : ℝ) * (q * (1 + B)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ D * (q * (1 + B)) := by
            refine mul_le_mul_of_nonneg_right (hcard L hL _ ?_) (mul_nonneg hq0 (by linarith))
            intro x hx
            obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hx
            exact (hf' Λ hΛ).1
        _ = B := by rw [← mul_assoc]; exact hfix
  exact main (C.sup (i L)) L hL C hC hLC fun Λ hΛ => Finset.le_sup hΛ

end GlobalTheory.HermNbr

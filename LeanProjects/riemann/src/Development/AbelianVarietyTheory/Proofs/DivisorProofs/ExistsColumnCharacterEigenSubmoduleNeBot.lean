import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem exists_eigenvector_of_stable {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : (ι → F) → V →ₗ[ℂ] V) (h0 : T 0 = LinearMap.id) (hT : ∀ x x' v, T x (T x' v) = T (x + x') v)
    (W : Submodule ℂ V) (hW : ∀ x, ∀ v ∈ W, T x v ∈ W) (hne : W ≠ ⊥) :
    ∃ l : ι → F, ∃ w ∈ W, w ≠ 0 ∧ ∀ x, T x w = ψ (∑ i, l i * x i) • w := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
  let w : (ι → F) → V := fun l => ∑ x : ι → F, ψ (-∑ i, l i * x i) • T x v
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have hs : ∀ x : ι → F, x ≠ 0 → ∑ l : ι → F, ψ (-∑ i, l i * x i) = 0 := by
    intro x hx
    have e : ∀ l : ι → F, ψ (-∑ i, l i * x i) = ∏ i, ψ (l i * (-x i)) := by
      intro l
      rw [← Finset.sum_neg_distrib]
      simp only [mul_neg]
      induction (Finset.univ : Finset ι) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    simp only [e]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun i t => ψ (t * (-x i)))]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := AddChar.sum_mulShift (ψ := ψ) (-x i) hprim
    rw [if_neg (by simpa using hi)] at this
    simpa using this
  have hsum : ∑ l, w l = (Fintype.card (ι → F) : ℂ) • v := by
    simp only [w]
    rw [Finset.sum_comm, Finset.sum_eq_single (0 : ι → F)]
    · simp [h0, Nat.cast_smul_eq_nsmul, -Fintype.card_pi]
    · intro x _ hx
      rw [← Finset.sum_smul, hs x hx, zero_smul]
    · simp
  have hex : ∃ l, w l ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero fun l _ => hc l] at hsum
    rcases smul_eq_zero.1 hsum.symm with h | h
    · exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h
    · exact hv0 h
  obtain ⟨l, hl⟩ := hex
  refine ⟨l, w l, W.sum_mem fun x _ => W.smul_mem _ (hW x v hv), hl, fun x => ?_⟩
  simp only [w, map_sum, map_smul, hT, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun z => ?_
  simp only [Equiv.coe_addLeft, ← AddChar.map_add_eq_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 2
  ring

variable {F : Type} [Field F] {r : ℕ}

def colMat (k : Fin r) (x : Fin r → F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if i < k ∧ j = k then x i else 0

theorem colMat_mul_apply (k : Fin r) (x : Fin r → F) (M : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    (colMat k x * M) i j = if i < k then x i * M k j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · by_cases h : i < k <;> simp [colMat, h]
  · intro m _ hm
    simp [colMat, hm]
  · simp

theorem one_add_colMat_mul (k : Fin r) (x x' : Fin r → F) :
    (1 + colMat k x) * (1 + colMat k x') = 1 + colMat k (x + x') := by
  have : colMat k x * colMat k x' = 0 := by
    ext i j
    rw [colMat_mul_apply]
    simp [colMat]
  have h2 : colMat k (x + x') = colMat k x + colMat k x' := by
    ext i j
    simp only [colMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h2, add_mul, mul_add, mul_add, this]
  simp only [one_mul, mul_one]
  abel

theorem colMat_zero (k : Fin r) : colMat k (0 : Fin r → F) = 0 := by
  ext i j
  simp [colMat]

def colGL (k : Fin r) (x : Fin r → F) : GL (Fin r) F where
  val := 1 + colMat k x
  inv := 1 + colMat k (-x)
  val_inv := by rw [one_add_colMat_mul]; simp [colMat_zero]
  inv_val := by rw [one_add_colMat_mul]; simp [colMat_zero]

theorem colGL_mem_unip (k : Fin r) (x : Fin r → F) : colGL k x ∈ unip F r := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    have : ¬ (i < k ∧ j = k) := fun h => by
      obtain ⟨h1, rfl⟩ := h
      exact lt_asymm h1 hij'
    simp [colGL, colMat, this, Matrix.one_apply_ne hij'.ne']
  · have : ¬ (i < k ∧ i = k) := fun h => h.1.ne h.2
    simp [colGL, colMat, this]

def colEl {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) : blockTri (κ := F) b :=
  ⟨colGL k x, fun i j hij => (colGL_mem_unip k x).1 (show j < i from hb.reflect_lt hij)⟩

theorem colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) :
    ((colEl hb k x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + colMat k x := rfl

theorem colEl_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x x' : Fin r → F) :
    colEl hb k x * colEl hb k x' = colEl hb k (x + x') :=
  Subtype.ext (Units.ext (one_add_colMat_mul k x x'))

theorem colEl_zero {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) : colEl hb k (0 : Fin r → F) = 1 :=
  Subtype.ext (Units.ext (by rw [colEl_val, colMat_zero]; simp))

theorem colEl_neg_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b k.val)
    (hx : ∀ i, i < k → x i = ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k) :
    colEl hb k (-x) * u ∈ colSet F b (k.val + 1) ∧
      edgeSum (blkEdge b) ((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) =
        edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
  have e : ∀ i j, (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j +
        if i < k then -x i * ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k j else 0 := by
    intro i j
    rw [Subgroup.coe_mul, Units.val_mul, colEl_val, add_mul, one_mul, Matrix.add_apply, colMat_mul_apply]
    rfl
  have hc : ∀ i j : Fin r, j.val < k.val + 1 →
      (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
        (1 : Matrix (Fin r) (Fin r) F) i j := by
    intro i j hj
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [hu.2 i j h, hu.2 k j h, Matrix.one_apply_ne (i := k) (j := j) (fun h' => by simp [h'] at h)]
      simp
    · obtain rfl : j = k := Fin.ext h
      rw [hu.1.2 j]
      rcases lt_trichotomy i j with h' | h' | h'
      · rw [if_pos h', hx i h', Matrix.one_apply_ne h'.ne]; ring
      · subst h'; simp [hu.1.2 i]
      · rw [if_neg (lt_asymm h'), hu.1.1 (show j.val < i.val from h'), Matrix.one_apply_ne h'.ne']; simp
  refine ⟨⟨(unip F r).mul_mem (colGL_mem_unip k (-x)) hu.1, hc⟩, ?_⟩
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : blkEdge b i j
  · have h1 := hij.1
    by_cases hk : k < j
    · have : ¬ i < k := by rw [Fin.lt_def] at hk ⊢; omega
      rw [if_pos hij, if_pos ⟨hij, hk⟩, e, if_neg this, add_zero]
    · rw [if_pos hij, if_neg (fun h => hk h.2), hc i j (by rw [Fin.lt_def] at hk; omega),
        Matrix.one_apply_ne (fun h' => by simp [h'] at h1)]
  · rw [if_neg hij, if_neg (fun h => hij h.1)]

theorem mul_colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b (k.val + 1)) (i j : Fin r) :
    (((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j + if i < k ∧ j = k then x i else 0 := by
  rw [Subgroup.coe_mul, Units.val_mul, colEl_val, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  have : ∀ m, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i m * colMat k x m j =
      (1 : Matrix (Fin r) (Fin r) F) i m * colMat k x m j := by
    intro m
    by_cases hm : m < k
    · rw [hu.2 i m (by rw [Fin.lt_def] at hm; omega)]
    · simp [colMat, hm]
  simp only [this]
  rw [← Matrix.mul_apply, one_mul]
  rfl

theorem colEl_stable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar F ℂ) {b : Fin r → ℕ} (hb : Monotone b)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (x : Fin r → F) (v : V)
    (hv : v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F)))) :
    σ (colEl hb k x) v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  rw [mem_eig] at hv ⊢
  intro u hu
  have hu' : u ∈ colSet F b k.val := ⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩
  have hm : u * colEl hb k x ∈ colSet F b k.val := by
    refine ⟨(unip F r).mul_mem hu.1 (colGL_mem_unip k x), fun i j hj => ?_⟩
    rw [mul_colEl_val hb k x hu, hu.2 i j (by omega), if_neg (fun h => by simp [h.2] at hj), add_zero]
  obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hm (fun i hi => by
    rw [mul_colEl_val hb k x hu, hu.2 i k (by omega), if_pos ⟨hi, rfl⟩, Matrix.one_apply_ne hi.ne, zero_add])
  obtain ⟨-, h3⟩ := colEl_neg_mul hb k 0 hu' (fun i hi => by
    rw [hu.2 i k (by omega), Matrix.one_apply_ne hi.ne]; rfl)
  rw [neg_zero, colEl_zero, one_mul] at h3
  have h4 : edgeSum (fun i j => blkEdge b i j ∧ k < j) ((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) =
      edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
    unfold edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [mul_colEl_val hb k x hu, if_neg (fun h' => h.2.ne' h'.2), add_zero]
    · rfl
  have h5 := hv _ h1
  rw [h2, h4, ← h3] at h5
  have h6 : u * colEl hb k x = colEl hb k x * (colEl hb k (-x) * (u * colEl hb k x)) := by
    rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
  rw [← Module.End.mul_apply, ← map_mul, h6, map_mul, Module.End.mul_apply, h5, map_smul]

theorem exists_colChar_eig_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  intro F _ _ ψ hψ r V _ _ b σ hb hinf k hne
  obtain ⟨l, w, hw, hw0, hl⟩ := exists_eigenvector_of_stable ψ hψ (fun x => σ (colEl hb k x))
    (by rw [colEl_zero, map_one]; rfl)
    (fun x x' v => by rw [← Module.End.mul_apply, ← map_mul, colEl_mul]) _
    (fun x v hv => colEl_stable ψ hb σ k x v hv) hne
  refine ⟨l, fun i hi => ?_, (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩⟩
  · by_contra hc
    refine AddChar.IsPrimitive.of_ne_one hψ hi (AddChar.ext _ _ fun t => ?_)
    have h1 : σ (colEl hb k (Pi.single i t)) = 1 := by
      refine hinf _ fun a c hac => ?_
      rw [colEl_val, Matrix.add_apply, add_eq_left]
      simp only [colMat, Matrix.of_apply]
      split_ifs with h
      · refine Pi.single_eq_of_ne (fun h' => hc ?_) _
        rw [← h', hac, h.2]
        exact ⟨h.2 ▸ h.1, rfl⟩
      · rfl
    have h2 := hl (Pi.single i t)
    rw [h1, Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), Pi.single_eq_same] at h2
    have h3 : (ψ (l i * t) - 1) • w = 0 := by rw [sub_smul, ← h2]; simp
    have h4 := (smul_eq_zero.1 h3).resolve_right hw0
    simpa [sub_eq_zero] using h4
  · rw [mem_eig] at hw ⊢
    intro u hu
    set x : Fin r → F := fun i => ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k with hx
    obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hu (fun i _ => rfl)
    have h5 := hw _ h1
    rw [h2] at h5
    have h6 : u = colEl hb k x * (colEl hb k (-x) * u) := by
      rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
    calc σ u w = σ (colEl hb k x) (σ (colEl hb k (-x) * u) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← h6]
      _ = _ := by
          rw [h5, map_smul, hl x, smul_smul, colChar, AddChar.map_add_eq_mul, mul_comm]

end GlobalTheory.FinGL.LeviWh

import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix

namespace LateralTheory.DivDb.UnitFactorizationTheorem
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

noncomputable def Dg (p : Fin n → Mat C N) (d : Fin n → C) : Mat C N := ∑ j, d j • p j

def S (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) : Set (Mat C N) :=
  {x | ∃ u ∈ Tv A p, ∃ d : Fin n → C, (∀ j, d j ≠ 0) ∧ x = u * Dg p d}

noncomputable def zT (p : Fin n → Mat C N) (T : Finset (Fin n)) : Mat C N := ∑ j ∈ T, p j

def Closed (E : Fin n → Fin n → Mat C N) (T : Finset (Fin n)) : Prop :=
  ∀ i j, E i j ≠ 0 → (i ∈ T ↔ j ∈ T)

section basic
variable {p : Fin n → Mat C N}

lemma pp (hp : Sys p) (i j : Fin n) : p i * p j = if i = j then p i else 0 := by
  split_ifs with h
  · subst h; exact (hp.1.idem i).eq
  · exact hp.1.ortho h

lemma sum_p (hp : Sys p) : ∑ j, p j = 1 := hp.1.complete

lemma Dg_p (hp : Sys p) (d : Fin n → C) (i : Fin n) : Dg p d * p i = d i • p i := by
  simp [Dg, Finset.sum_mul, smul_mul_assoc, pp hp]

lemma p_Dg (hp : Sys p) (d : Fin n → C) (i : Fin n) : p i * Dg p d = d i • p i := by
  simp [Dg, Finset.mul_sum, mul_smul_comm, pp hp]

lemma Dg_mul (hp : Sys p) (a b : Fin n → C) : Dg p a * Dg p b = Dg p (a * b) := by
  conv_lhs => rw [Dg, Finset.sum_mul]
  simp only [smul_mul_assoc, p_Dg hp, smul_smul]
  simp [Dg, Pi.mul_apply]

lemma Dg_one (hp : Sys p) : Dg p 1 = 1 := by simp [Dg, sum_p hp]

lemma zT_p (hp : Sys p) (T : Finset (Fin n)) (i : Fin n) :
    zT p T * p i = if i ∈ T then p i else 0 := by
  simp [zT, Finset.sum_mul, pp hp]

lemma p_zT (hp : Sys p) (T : Finset (Fin n)) (i : Fin n) :
    p i * zT p T = if i ∈ T then p i else 0 := by
  simp [zT, Finset.mul_sum, pp hp]

lemma zT_idem (hp : Sys p) (T : Finset (Fin n)) : zT p T * zT p T = zT p T := by
  have h : zT p T * zT p T = ∑ j ∈ T, zT p T * p j := Finset.mul_sum _ _ _
  rw [h]
  exact Finset.sum_congr rfl fun j hj => by rw [zT_p hp, if_pos hj]

lemma zT_orth (hp : Sys p) {T T' : Finset (Fin n)} (hd : Disjoint T T') : zT p T * zT p T' = 0 := by
  conv_lhs => rw [show zT p T' = ∑ j ∈ T', p j from rfl, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj => by rw [zT_p hp, if_neg (Finset.disjoint_right.mp hd hj)]

lemma decomp (hp : Sys p) (a : Mat C N) : a = ∑ i, ∑ j, p i * a * p j := by
  conv_lhs => rw [← one_mul a, ← mul_one (1 * a), ← sum_p hp]
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

variable {A : Subalgebra C (Mat C N)}

lemma conj_Tv (hp : Sys p) {d : Fin n → C} (hd : ∀ j, d j ≠ 0) {u : Mat C N} (hu : u ∈ Tv A p) :
    Dg p d * u * Dg p d⁻¹ ∈ Tv A p := by
  have hdd : d * d⁻¹ = 1 := funext fun j => mul_inv_cancel₀ (hd j)
  have hdd' : d⁻¹ * d = 1 := funext fun j => inv_mul_cancel₀ (hd j)
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, j, k, hjk, rfl⟩ := hx
    apply Submonoid.subset_closure
    refine ⟨(d j * (d k)⁻¹) • a, A.smul_mem ha _, j, k, hjk, ?_⟩
    have e1 : Dg p d * (p j * a * p k) * Dg p d⁻¹ = (d j * (d k)⁻¹) • (p j * a * p k) := by
      rw [← mul_assoc, ← mul_assoc, Dg_p hp, mul_assoc _ (p k), p_Dg hp]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Pi.inv_apply]
      rw [mul_comm ((d k)⁻¹)]
    rw [mul_add, add_mul, mul_one, Dg_mul hp, hdd, Dg_one hp, e1, mul_smul_comm, smul_mul_assoc]
  | one => rw [mul_one, Dg_mul hp, hdd, Dg_one hp]; exact one_mem _
  | mul x y _ _ hx hy =>
    have h' : Dg p d⁻¹ * Dg p d = 1 := by rw [Dg_mul hp, hdd', Dg_one hp]
    have : Dg p d * (x * y) * Dg p d⁻¹ = (Dg p d * x * Dg p d⁻¹) * (Dg p d * y * Dg p d⁻¹) := by
      simp only [mul_assoc]; rw [← mul_assoc (Dg p d⁻¹) (Dg p d), h', one_mul]
    rw [this]; exact mul_mem hx hy

lemma S_mul (hp : Sys p) {x y : Mat C N} (hx : x ∈ S A p) (hy : y ∈ S A p) : x * y ∈ S A p := by
  obtain ⟨u, hu, d, hd, rfl⟩ := hx
  obtain ⟨u', hu', d', hd', rfl⟩ := hy
  refine ⟨u * (Dg p d * u' * Dg p d⁻¹), mul_mem hu (conj_Tv hp hd hu'), d * d',
    fun j => mul_ne_zero (hd j) (hd' j), ?_⟩
  have hdd' : d⁻¹ * d = 1 := funext fun j => inv_mul_cancel₀ (hd j)
  have h' : Dg p d⁻¹ * Dg p d = 1 := by rw [Dg_mul hp, hdd', Dg_one hp]
  rw [← Dg_mul hp]
  simp only [mul_assoc]; rw [← mul_assoc (Dg p d⁻¹) (Dg p d), h', one_mul]

lemma one_S (hp : Sys p) : (1 : Mat C N) ∈ S A p :=
  ⟨1, one_mem _, 1, fun _ => one_ne_zero, by rw [Dg_one hp, one_mul]⟩

lemma Tv_S (hp : Sys p) {u : Mat C N} (hu : u ∈ Tv A p) : u ∈ S A p :=
  ⟨u, hu, 1, fun _ => one_ne_zero, by rw [Dg_one hp, mul_one]⟩

lemma Dg_S {d : Fin n → C} (hd : ∀ j, d j ≠ 0) : Dg p d ∈ S A p :=
  ⟨1, one_mem _, d, hd, (one_mul _).symm⟩

end basic

section mu
variable {p : Fin n → Mat C N} {A : Subalgebra C (Mat C N)} {E : Fin n → Fin n → Mat C N}

lemma p_E (hp : Sys p) (hE : MUnits A p E) (k i j : Fin n) :
    p k * E i j = if k = i then E i j else 0 := by
  have h := hE.2.2.1 i j
  conv_lhs => rw [← h]
  rw [← mul_assoc, ← mul_assoc, pp hp]
  split_ifs with h'
  · subst h'; exact h
  · simp

lemma E_p (hp : Sys p) (hE : MUnits A p E) (i j k : Fin n) :
    E i j * p k = if j = k then E i j else 0 := by
  have h := hE.2.2.1 i j
  conv_lhs => rw [← h]
  rw [mul_assoc, pp hp]
  split_ifs with h'
  · subst h'; exact h
  · simp

lemma E_E_ne (hp : Sys p) (hE : MUnits A p E) {i j k l : Fin n} (hjk : j ≠ k) : E i j * E k l = 0 := by
  have h := hE.2.2.1 k l
  conv_lhs => rw [← h]
  rw [← mul_assoc, ← mul_assoc, E_p hp hE, if_neg hjk, zero_mul, zero_mul]

lemma zT_E (hp : Sys p) (hE : MUnits A p E) (T : Finset (Fin n)) (i j : Fin n) :
    zT p T * E i j = if i ∈ T then E i j else 0 := by
  have h : p i * E i j = E i j := by rw [p_E hp hE, if_pos rfl]
  conv_lhs => rw [← h]
  rw [← mul_assoc, zT_p hp]
  split_ifs <;> simp [h]

lemma E_zT (hp : Sys p) (hE : MUnits A p E) (T : Finset (Fin n)) (i j : Fin n) :
    E i j * zT p T = if j ∈ T then E i j else 0 := by
  have h : E i j * p j = E i j := by rw [E_p hp hE, if_pos rfl]
  conv_lhs => rw [← h]
  rw [mul_assoc, p_zT hp]
  split_ifs <;> simp [h]

lemma zT_comm (hp : Sys p) (hE : MUnits A p E) {T : Finset (Fin n)} (hT : Closed E T)
    {a : Mat C N} (ha : a ∈ A) : zT p T * a = a * zT p T := by
  rw [decomp hp a]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨c, hc⟩ := hE.2.2.2.2.2 a ha i j
  rw [hc, mul_smul_comm, smul_mul_assoc, zT_E hp hE, E_zT hp hE]
  by_cases hij : E i j = 0
  · simp [hij]
  · simp only [hT i j hij]

open Classical in
noncomputable def Bk (E : Fin n → Fin n → Mat C N) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => E r j ≠ 0)

lemma mem_Bk {r j : Fin n} : j ∈ Bk E r ↔ E r j ≠ 0 := by simp [Bk]

lemma E_ne (hE : MUnits A p E) {i j k : Fin n} (h1 : E i j ≠ 0) (h2 : E j k ≠ 0) : E i k ≠ 0 :=
  (hE.2.2.2.2.1 i j k h1 h2).2

lemma closed_Bk (hE : MUnits A p E) (r : Fin n) : Closed E (Bk E r) := fun i j hij => by
  simp only [mem_Bk]
  exact ⟨fun h => E_ne hE h hij, fun h => E_ne hE h (hE.2.2.2.1 i j hij)⟩

lemma closed_sdiff {T T' : Finset (Fin n)} (h : Closed E T) (h' : Closed E T') : Closed E (T \ T') :=
  fun i j hij => by simp only [Finset.mem_sdiff, h i j hij, h' i j hij]

end mu

section block
variable {p : Fin n → Mat C N} {A : Subalgebra C (Mat C N)} {E : Fin n → Fin n → Mat C N} {r : Fin n}

noncomputable def X (E : Fin n → Fin n → Mat C N) (r : Fin n)
    (M : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) : Mat C N := ∑ i, ∑ j, M i j • E i j

noncomputable def Ψ (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N) (r : Fin n)
    (M : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) : Mat C N := 1 - zT p (Bk E r) + X E r M

lemma zT_Bk : zT p (Bk E r) = ∑ j : {j // j ∈ Bk E r}, p j :=
  (Finset.sum_coe_sort _ _).symm

lemma EK (hE : MUnits A p E) (i j : {j // j ∈ Bk E r}) : E i j ≠ 0 :=
  E_ne hE (hE.2.2.2.1 r i (mem_Bk.mp i.2)) (mem_Bk.mp j.2)

lemma EE_same (hE : MUnits A p E) (i j l : {j // j ∈ Bk E r}) : E i j * E j l = E i l :=
  (hE.2.2.2.2.1 i j l (EK hE i j) (EK hE j l)).1

lemma EE_ne (hp : Sys p) (hE : MUnits A p E) (i : {j // j ∈ Bk E r}) {j k : {j // j ∈ Bk E r}}
    (l : {j // j ∈ Bk E r}) (hjk : j ≠ k) : E i j * E k l = 0 :=
  E_E_ne hp hE (fun h => hjk (Subtype.ext h))

lemma X_mul (hp : Sys p) (hE : MUnits A p E) (M M' : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) :
    X E r (M * M') = X E r M * X E r M' := by
  rw [X, X, X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  simp only [Matrix.mul_apply, Finset.sum_smul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  symm
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_mul_smul_comm, EE_same hE]
  · intro k _ hk
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => by rw [smul_mul_smul_comm, EE_ne hp hE i l (Ne.symm hk), smul_zero]
  · simp

lemma X_add (M M' : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) : X E r (M + M') = X E r M + X E r M' := by
  simp [X, add_smul, Finset.sum_add_distrib]

lemma X_zero : X E r 0 = 0 := by simp [X]

lemma X_one (hE : MUnits A p E) : X E r 1 = zT p (Bk E r) := by
  rw [zT_Bk]
  simp [X, Matrix.one_apply, ite_smul, hE.2.1]

lemma X_single (i j : {j // j ∈ Bk E r}) (c : C) : X E r (Matrix.single i j c) = c • E i j := by
  simp [X, Matrix.single_apply, ite_smul, ite_and]

lemma X_diag (hE : MUnits A p E) (D : {j // j ∈ Bk E r} → C) :
    X E r (Matrix.diagonal D) = ∑ i : {j // j ∈ Bk E r}, D i • p i := by
  simp [X, Matrix.diagonal_apply, ite_smul, hE.2.1]

lemma zT_X (hp : Sys p) (hE : MUnits A p E) (M : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) :
    zT p (Bk E r) * X E r M = X E r M := by
  simp only [X, Finset.mul_sum, mul_smul_comm, zT_E hp hE]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [if_pos i.2]

lemma X_zT (hp : Sys p) (hE : MUnits A p E) (M : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) :
    X E r M * zT p (Bk E r) = X E r M := by
  simp only [X, Finset.sum_mul, smul_mul_assoc, E_zT hp hE]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [if_pos j.2]

lemma Ψ_mul (hp : Sys p) (hE : MUnits A p E) (M M' : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C) :
    Ψ p E r (M * M') = Ψ p E r M * Ψ p E r M' := by
  simp only [Ψ, X_mul hp hE, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, zT_idem hp,
    zT_X hp hE, X_zT hp hE]
  abel

lemma pXp (hp : Sys p) (hE : MUnits A p E) (M : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C)
    (i j : {j // j ∈ Bk E r}) : p i * X E r M * p j = M i j • E i j := by
  simp only [X, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, p_E hp hE, E_p hp hE,
    ite_mul, zero_mul, Subtype.val_inj]
  simp [smul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

end block

section final
variable {p : Fin n → Mat C N} {A : Subalgebra C (Mat C N)} {E : Fin n → Fin n → Mat C N} {r : Fin n}

lemma Ψ_trans (hp : Sys p) (hE : MUnits A p E) (t : TransvectionStruct {j // j ∈ Bk E r} C) :
    Ψ p E r t.toMatrix ∈ S A p := by
  apply Tv_S hp
  have h : Ψ p E r t.toMatrix = 1 + p t.i * (t.c • E t.i t.j) * p t.j := by
    rw [Ψ, TransvectionStruct.toMatrix, transvection, X_add, X_one hE, X_single, mul_smul_comm,
      smul_mul_assoc, hE.2.2.1]
    abel
  rw [h]
  exact Submonoid.subset_closure
    ⟨_, A.smul_mem (hE.1 _ _) _, t.i, t.j, fun h => t.hij (Subtype.ext h), rfl⟩

noncomputable def dd (E : Fin n → Fin n → Mat C N) (r : Fin n) (D : {j // j ∈ Bk E r} → C) :
    Fin n → C := fun j => if h : j ∈ Bk E r then D ⟨j, h⟩ else 1

lemma Ψ_diag (hp : Sys p) (hE : MUnits A p E) (D : {j // j ∈ Bk E r} → C) :
    Ψ p E r (Matrix.diagonal D) = Dg p (dd E r D) := by
  have h1 := Finset.sum_add_sum_compl (Bk E r) p
  have h2 := Finset.sum_add_sum_compl (Bk E r) (fun j => dd E r D j • p j)
  rw [sum_p hp] at h1
  have h3 : ∑ j ∈ Bk E r, dd E r D j • p j = ∑ j : {j // j ∈ Bk E r}, D j • p j := by
    rw [← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun j _ => by simp [dd, j.2]
  have h4 : ∑ j ∈ (Bk E r)ᶜ, dd E r D j • p j = ∑ j ∈ (Bk E r)ᶜ, p j :=
    Finset.sum_congr rfl fun j hj => by simp [dd, Finset.mem_compl.mp hj]
  rw [Ψ, X_diag hE, Dg, ← h2, h3, h4, ← h1]
  unfold zT
  abel

lemma block (hp : Sys p) (hE : MUnits A p E) (r : Fin n) {v : Mat C N} (hv : v ∈ A) (hu : IsUnit v) :
    1 - zT p (Bk E r) + zT p (Bk E r) * v ∈ S A p := by
  choose c hc using hE.2.2.2.2.2 v hv
  let M : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C := fun i j => c i j
  have hcomm := zT_comm hp hE (closed_Bk hE r) hv
  have hXM : X E r M = zT p (Bk E r) * v := by
    have : X E r M = zT p (Bk E r) * v * zT p (Bk E r) := by
      rw [zT_Bk, Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.mul_sum, X]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hc i j).symm
    rw [this, mul_assoc, ← hcomm, ← mul_assoc, zT_idem hp]
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    let M'' : Matrix {j // j ∈ Bk E r} {j // j ∈ Bk E r} C := fun i _ => w i
    have hMM : M * M'' = 0 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.zero_apply]
      exact congrFun hw i
    have h1 : v * X E r M'' = 0 := by
      have h := X_mul hp hE M M''
      rw [hMM, X_zero, hXM] at h
      rw [← zT_X hp hE M'', ← mul_assoc, ← hcomm, h.symm]
    have h2 : X E r M'' = 0 := hu.mul_right_eq_zero.mp h1
    apply hw0
    funext i
    have := pXp hp hE M'' i i
    rw [h2, mul_zero, zero_mul, hE.2.1] at this
    exact (smul_eq_zero.mp this.symm).resolve_right (hp.2 i)
  have hP := Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => Ψ p E r M ∈ S A p) M hdet
    (fun D hD => by
      show Ψ p E r (Matrix.diagonal D) ∈ S A p
      rw [Ψ_diag hp hE]
      refine Dg_S fun j => ?_
      rw [Matrix.det_diagonal] at hD
      by_cases hj : j ∈ Bk E r
      · simp only [dd, dif_pos hj]; exact Finset.prod_ne_zero_iff.mp hD _ (Finset.mem_univ _)
      · simp [dd, hj])
    (fun t => Ψ_trans hp hE t)
    (fun A' B' _ _ hA hB => by
      show Ψ p E r (A' * B') ∈ S A p
      rw [Ψ_mul hp hE]; exact S_mul hp hA hB)
  have : Ψ p E r M = 1 - zT p (Bk E r) + zT p (Bk E r) * v := by rw [Ψ, hXM]
  rw [← this]; exact hP

lemma main (hp : Sys p) (hE : MUnits A p E) {v : Mat C N} (hv : v ∈ A) (hu : IsUnit v) :
    ∀ T : Finset (Fin n), Closed E T → 1 - zT p T + zT p T * v ∈ S A p := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
    · simp only [zT, Finset.sum_empty, sub_zero, zero_mul, add_zero]; exact one_S hp
    · have hrB : r ∈ Bk E r := mem_Bk.mpr (by rw [hE.2.1]; exact hp.2 r)
      have hBT : Bk E r ⊆ T := fun j hj => (hT r j (mem_Bk.mp hj)).mp hr
      have hT' : Closed E (T \ Bk E r) := closed_sdiff hT (closed_Bk hE r)
      have hlt : T \ Bk E r ⊂ T := Finset.sdiff_ssubset hBT ⟨r, hrB⟩
      have ih' := ih _ hlt hT'
      have hsplit : zT p T = zT p (T \ Bk E r) + zT p (Bk E r) := (Finset.sum_sdiff hBT).symm
      have hBT0 : zT p (Bk E r) * zT p (T \ Bk E r) = 0 := zT_orth hp Finset.disjoint_sdiff
      have hc' := zT_comm hp hE hT' hv
      have e1 : zT p (Bk E r) * v * zT p (T \ Bk E r) = 0 := by
        rw [mul_assoc, ← hc', ← mul_assoc, hBT0, zero_mul]
      have e2 : zT p (Bk E r) * v * (zT p (T \ Bk E r) * v) = 0 := by rw [← mul_assoc, e1, zero_mul]
      have e3 : zT p (Bk E r) * (zT p (T \ Bk E r) * v) = 0 := by rw [← mul_assoc, hBT0, zero_mul]
      have key : 1 - zT p T + zT p T * v = (1 - zT p (Bk E r) + zT p (Bk E r) * v) *
          (1 - zT p (T \ Bk E r) + zT p (T \ Bk E r) * v) := by
        rw [hsplit]
        simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, hBT0, e1, e2, e3]
        abel
      rw [key]; exact S_mul hp (block hp hE r hv hu) ih'

end final

theorem UnitFactor_of : LateralTheory.DivDb.UnitFactorization := by
  intro C _ N n A p E hp hE v hv hu
  have h := main hp hE hv hu Finset.univ (fun _ _ _ => by simp)
  have hz : zT p Finset.univ = 1 := sum_p hp
  rw [hz, sub_self, zero_add, one_mul] at h
  obtain ⟨u, hu', d, hd, h'⟩ := h
  exact ⟨u, hu', d, hd, h'⟩

end LateralTheory.DivDb.UnitFactorizationTheorem

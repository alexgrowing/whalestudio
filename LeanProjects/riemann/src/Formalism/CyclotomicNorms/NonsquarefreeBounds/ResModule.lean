import Formalism.CyclotomicNorms.StatementTW

open Polynomial Matrix

namespace Formalism.CyclotomicNorms
noncomputable section

namespace residueMatrixData

section SNF
variable {R : Type*} [CommRing R]

lemma exists_dvd_all_of_total (hR : ∀ x y : R, x ∣ y ∨ y ∣ x) {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → R) : ∃ i ∈ s, ∀ j ∈ s, f i ∣ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with h | h
    · exact ⟨a, by simp, by simp [h]⟩
    obtain ⟨i, hi, hij⟩ := ih h
    rcases hR (f a) (f i) with h' | h'
    · refine ⟨a, by simp, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact dvd_refl _
      · exact h'.trans (hij j hj)
    · refine ⟨i, by simp [hi], ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h'
      · exact hij j hj

def ext1 {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : Matrix (Fin (a+1)) (Fin (a+1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => P i' j') j) i

@[simp] lemma blockExtend_zero_zero {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : ext1 P 0 0 = 1 := rfl
@[simp] lemma blockExtend_zero_succ {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (j : Fin a) : ext1 P 0 j.succ = 0 := rfl
@[simp] lemma blockExtend_succ_zero {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (i : Fin a) : ext1 P i.succ 0 = 0 := rfl
@[simp] lemma blockExtend_succ_succ {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    ext1 P i.succ j.succ = P i j := rfl

lemma det_blockExtend {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : (ext1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockExtend_zero_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, blockExtend_zero_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  congr 1

lemma blockExtend_mul_mul_eq_diagonal {a : ℕ} (P Q : Matrix (Fin a) (Fin a) R) (E : Matrix (Fin (a+1)) (Fin (a+1)) R)
    (h1 : ∀ j : Fin a, E 0 j.succ = 0) (h2 : ∀ i : Fin a, E i.succ 0 = 0) (d : Fin a → R)
    (hd : P * (Matrix.of fun i j : Fin a => E i.succ j.succ) * Q = diagonal d) :
    ext1 P * E * ext1 Q = diagonal (Fin.cons (E 0 0) d) := by
  ext i j
  have hd' : ∀ i j, (P * (Matrix.of fun i j : Fin a => E i.succ j.succ) * Q) i j = diagonal d i j := by
    rw [hd]; intros; rfl
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, diagonal_apply, (Fin.succ_ne_zero j).symm]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, diagonal_apply, (Fin.succ_ne_zero i)]
  · have := hd' i j
    simp only [Matrix.mul_apply, Matrix.of_apply] at this
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, diagonal_apply]
    rw [this, diagonal_apply]

lemma isUnit_det_swap {a : ℕ} (i j : Fin a) : IsUnit (Matrix.swap R i j).det :=
  isUnit_iff_exists_inv.mpr ⟨(Matrix.swap R i j).det, by rw [← Matrix.det_mul, swap_mul_self, det_one]⟩

theorem exists_diag (hR : ∀ x y : R, x ∣ y ∨ y ∣ x) : ∀ (a : ℕ) (M : Matrix (Fin a) (Fin a) R),
    ∃ P Q : Matrix (Fin a) (Fin a) R, IsUnit P.det ∧ IsUnit Q.det ∧
      ∃ d : Fin a → R, P * M * Q = diagonal d := by
  intro a
  induction a with
  | zero => intro M; exact ⟨1, 1, by simp, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ a ih =>
    intro M
    obtain ⟨⟨i0, j0⟩, -, hp⟩ := exists_dvd_all_of_total hR (Finset.univ : Finset (Fin (a+1) × Fin (a+1)))
      Finset.univ_nonempty (fun p => M p.1 p.2)
    set M1 := Matrix.swap R 0 i0 * M * Matrix.swap R 0 j0 with hM1
    have h00 : M1 0 0 = M i0 j0 := by simp [hM1]
    have hdvd : ∀ i j, M1 0 0 ∣ M1 i j := by
      intro i j
      rw [h00, hM1, Matrix.mul_apply]
      refine Finset.dvd_sum fun l _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.dvd_sum fun k _ => ?_
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hp (k, l) (Finset.mem_univ _)) _) _
    choose c hc using hdvd
    let Bl : Matrix (Fin (a+1)) (Fin (a+1)) R := Matrix.of fun i k => if i ≠ 0 ∧ k = 0 then c i 0 else 0
    let Br : Matrix (Fin (a+1)) (Fin (a+1)) R := Matrix.of fun k j => if k = 0 ∧ j ≠ 0 then c 0 j else 0
    have hL : (1 - Bl).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular]
      · refine Finset.prod_eq_one fun i _ => ?_
        simp [Bl]
      · intro i j hij
        have hj : j ≠ 0 := by
          intro h; subst h; exact (Fin.not_lt_zero i) hij
        simp [Bl, hj, Matrix.one_apply]
        rintro rfl; exact absurd hij (lt_irrefl _)
    have hU : (1 - Br).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular]
      · refine Finset.prod_eq_one fun i _ => ?_
        simp [Br]
      · intro i j hij
        have hi : i ≠ 0 := by
          intro h; subst h; exact (Fin.not_lt_zero j) hij
        simp [Br, hi, Matrix.one_apply]
        rintro rfl; exact absurd hij (lt_irrefl _)
    set E := (1 - Bl) * M1 * (1 - Br) with hE
    have hBl : ∀ i j, (Bl * M1) i j = if i ≠ 0 then c i 0 * M1 0 j else 0 := by
      intro i j
      simp only [Bl, Matrix.mul_apply, Matrix.of_apply]
      split_ifs with h <;> simp [h]
    have hBr : ∀ (X : Matrix (Fin (a+1)) (Fin (a+1)) R) i j,
        (X * Br) i j = if j ≠ 0 then X i 0 * c 0 j else 0 := by
      intro X i j
      simp only [Br, Matrix.mul_apply, Matrix.of_apply]
      split_ifs with h <;> simp [h]
    have hEij : ∀ i j, E i j = (M1 i j - if i ≠ 0 then c i 0 * M1 0 j else 0) -
        (if j ≠ 0 then (M1 i 0 - if i ≠ 0 then c i 0 * M1 0 0 else 0) * c 0 j else 0) := by
      intro i j
      rw [hE, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, hBr, Matrix.sub_mul, Matrix.one_mul,
        Matrix.sub_apply, Matrix.sub_apply, hBl, hBl]
    have hE00 : E 0 0 = M1 0 0 := by rw [hEij]; simp
    have hE1 : ∀ j : Fin a, E 0 j.succ = 0 := by
      intro j; rw [hEij]; simp [Fin.succ_ne_zero]; rw [hc 0 j.succ]; ring
    have hE2 : ∀ i : Fin a, E i.succ 0 = 0 := by
      intro i; rw [hEij]; simp [Fin.succ_ne_zero]; rw [hc i.succ 0]; ring
    obtain ⟨P', Q', hP', hQ', d', hd'⟩ := ih (Matrix.of fun i j : Fin a => E i.succ j.succ)
    refine ⟨ext1 P' * (1 - Bl) * Matrix.swap R 0 i0, Matrix.swap R 0 j0 * (1 - Br) * ext1 Q', ?_, ?_,
      Fin.cons (E 0 0) d', ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_blockExtend, hL, mul_one]
      exact hP'.mul (isUnit_det_swap _ _)
    · rw [Matrix.det_mul, Matrix.det_mul, det_blockExtend, hU, mul_one]
      exact (isUnit_det_swap _ _).mul hQ'
    · rw [← blockExtend_mul_mul_eq_diagonal P' Q' E hE1 hE2 d' hd', hE, hM1]
      simp only [Matrix.mul_assoc]

end SNF

section Trunc
variable {K' : Type} [Field K'] {n : ℕ}

local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

lemma tt_pow_n : (TT) ^ n = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

lemma tt_pow_ge {m : ℕ} (hm : n ≤ m) : (TT) ^ m = 0 := by
  rw [← Nat.add_sub_cancel' hm, pow_add, tt_pow_n, zero_mul]

lemma trunc_normal (x : TruncK K' n) : ∃ k ≤ n, ∃ u : TruncK K' n, IsUnit u ∧ x = u * (TT) ^ k := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases hp : p = 0
  · exact ⟨n, le_rfl, 1, isUnit_one, by simp [hp, tt_pow_n]⟩
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  simp only [map_zero, sub_zero] at hpq hq
  set m := rootMultiplicity 0 p
  by_cases hm : n ≤ m
  · refine ⟨n, le_rfl, 1, isUnit_one, ?_⟩
    rw [hpq, map_mul, map_pow, tt_pow_ge hm, tt_pow_n]; simp
  · replace hm := not_le.mp hm
    refine ⟨m, hm.le, Ideal.Quotient.mk _ q, ?_, ?_⟩
    · have hc : IsCoprime ((X : K'[X]) ^ n) q :=
        IsCoprime.pow_left ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hq)
      obtain ⟨u, v, huv⟩ := hc
      refine isUnit_iff_exists_inv'.mpr ⟨Ideal.Quotient.mk _ v, ?_⟩
      have : Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) (u * X ^ n + v * q) = 1 := by
        rw [huv, map_one]
      rw [map_add, map_mul, map_mul, map_pow, tt_pow_n, mul_zero, zero_add] at this
      exact this
    · rw [hpq, map_mul, map_pow, mul_comm]

lemma trunc_total (x y : TruncK K' n) : x ∣ y ∨ y ∣ x := by
  obtain ⟨k, hk, u, hu, rfl⟩ := trunc_normal x
  obtain ⟨l, hl, v, hv, rfl⟩ := trunc_normal y
  rcases le_total k l with h | h
  · left
    refine ⟨hu.unit⁻¹ * v * (TT) ^ (l - k), ?_⟩
    rw [← Nat.add_sub_cancel' h, pow_add]
    simp only [Nat.add_sub_cancel_left]
    calc v * ((TT) ^ k * (TT) ^ (l - k)) = (u * hu.unit⁻¹) * v * (TT) ^ k * (TT) ^ (l - k) := by
          rw [IsUnit.mul_val_inv]; ring
      _ = _ := by ring
  · right
    refine ⟨hv.unit⁻¹ * u * (TT) ^ (k - l), ?_⟩
    rw [← Nat.add_sub_cancel' h, pow_add]
    simp only [Nat.add_sub_cancel_left]
    calc u * ((TT) ^ l * (TT) ^ (k - l)) = (v * hv.unit⁻¹) * u * (TT) ^ l * (TT) ^ (k - l) := by
          rw [IsUnit.mul_val_inv]; ring
      _ = _ := by ring

lemma tt_pow_notMem {m C : ℕ} (hm : m ≤ C) (hC : C < n) :
    (TT) ^ m ∉ Ideal.span {(TT) ^ (C + 1)} := by
  rw [Ideal.mem_span_singleton]
  rintro ⟨y, hy⟩
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_pow, ← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hy
  have h1 : (X : K'[X]) ^ (C + 1) ∣ X ^ m - X ^ (C + 1) * q :=
    (pow_dvd_pow X (by omega : C + 1 ≤ n)).trans hy
  have h2 : (X : K'[X]) ^ (C + 1) ∣ X ^ m := by
    have := h1.add (dvd_mul_right ((X : K'[X]) ^ (C + 1)) q)
    simpa using this
  rw [Polynomial.X_pow_dvd_iff] at h2
  have := h2 m (by omega)
  rw [Polynomial.coeff_X_pow_self] at this
  exact one_ne_zero this

def pbT (K' : Type) [Field K'] (n : ℕ) : PowerBasis K' (TruncK K' n) :=
  AdjoinRoot.powerBasis' (monic_X_pow n)

instance (K' : Type) [Field K'] (n : ℕ) : FiniteDimensional K' (TruncK K' n) := (pbT K' n).finite

lemma tt_linIndep : LinearIndependent K' (fun i : Fin n => (TT) ^ (i : ℕ)) := by
  have h := (pbT K' n).basis.linearIndependent
  have hd : (pbT K' n).dim = n := by simp [pbT]
  have e : ∀ i : Fin (pbT K' n).dim, (pbT K' n).basis i = (TT) ^ (i : ℕ) := by
    intro i; rw [PowerBasis.basis_eq_pow]; rfl
  have h2 : LinearIndependent K' (fun i : Fin (pbT K' n).dim => (TT) ^ (i : ℕ)) := by
    convert h using 1
    · funext i; exact (e i).symm
    all_goals rfl
  exact h2.comp (Fin.cast hd.symm) (Fin.cast_injective _)

end Trunc

section Mod
variable {K' : Type} [Field K'] {n : ℕ}

local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

instance finite_sub {a : ℕ} (p : Submodule (TruncK K' n) (Fin a → TruncK K' n)) :
    Module.Finite K' ↥p :=
  Module.Finite.of_injective (p.subtype.restrictScalars K') Subtype.val_injective

lemma finrank_split {a : ℕ} (W N : Submodule (TruncK K' n) (Fin a → TruncK K' n)) (h : N ≤ W) :
    Module.finrank K' (W ⧸ N.comap W.subtype) + Module.finrank K' N = Module.finrank K' W := by
  have e1 := (Submodule.Quotient.restrictScalarsEquiv K' (N.comap W.subtype)).finrank_eq
  have e2 := ((Submodule.comapSubtypeEquivOfLe h).restrictScalars K').finrank_eq
  rw [← e1, ← e2]
  exact Submodule.finrank_quotient_add_finrank ((N.comap W.subtype).restrictScalars K')

lemma eq_bot_of_noTorsion {a : ℕ} (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (h : ∀ x ∈ N, (TT) • x = 0 → x = 0) : N = ⊥ := by
  have key : ∀ m : ℕ, ∀ y ∈ N, (TT) ^ m • y = 0 → y = 0 := by
    intro m
    induction m with
    | zero => intro y _ hy; simpa using hy
    | succ m ih =>
      intro y hy h0
      apply ih y hy
      apply h _ (N.smul_mem _ hy)
      rw [← mul_smul, ← pow_succ']; exact h0
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  exact key n y hy (by rw [tt_pow_n, zero_smul])

lemma finrank_span_le {a m : ℕ} (x : Fin a → TruncK K' n) (hx : (TT) ^ m • x = 0) :
    Module.finrank K' ↥(Submodule.span (TruncK K' n) {x}) ≤ m := by
  have hle : (Submodule.span (TruncK K' n) {x}).restrictScalars K' ≤
      Submodule.span K' (Set.range (fun j : Fin m => (TT) ^ (j : ℕ) • x)) := by
    intro y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, add_smul]
      exact Submodule.add_mem _ (hp (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        (hq (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
    | monomial j c =>
      have e : (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) (monomial j c) : TruncK K' n) =
          algebraMap K' (TruncK K' n) c * (TT) ^ j := by
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        rfl
      rw [e, mul_smul, algebraMap_smul]
      apply Submodule.smul_mem
      by_cases hj : j < m
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · rw [← Nat.sub_add_cancel (not_lt.mp hj), pow_add, mul_smul, hx, smul_zero]
        exact Submodule.zero_mem _
  calc Module.finrank K' ↥(Submodule.span (TruncK K' n) {x})
      = Module.finrank K' ↥((Submodule.span (TruncK K' n) {x}).restrictScalars K') := rfl
    _ ≤ Module.finrank K' ↥(Submodule.span K' (Set.range (fun j : Fin m => (TT) ^ (j : ℕ) • x))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin m) := finrank_range_le_card _
    _ = m := Fintype.card_fin m

end Mod

section Cyc
variable {K' : Type} [Field K'] {n : ℕ}

local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

lemma cyclic_of_socle {a : ℕ} (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (hN : Module.finrank K' ↥(N ⊓ LinearMap.ker ((TT) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1) :
    ∃ x, N = Submodule.span (TruncK K' n) {x} := by
  classical
  set S := N ⊓ LinearMap.ker ((TT) • LinearMap.id :
    (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n)) with hS
  have memS : ∀ y, y ∈ S ↔ y ∈ N ∧ (TT) • y = 0 := by
    intro y; simp [hS]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hN
  have hex : ∃ h : ℕ, ∀ y ∈ N, (TT) ^ h • y = 0 := ⟨n, fun y _ => by rw [tt_pow_n, zero_smul]⟩
  by_cases hz : Nat.find hex = 0
  · refine ⟨0, ?_⟩
    have h0 := Nat.find_spec hex
    rw [hz] at h0
    rw [Submodule.span_singleton_eq_bot.mpr rfl, eq_bot_iff]
    intro y hy
    simpa using h0 y hy
  obtain ⟨h, hh⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have hspec : ∀ y ∈ N, (TT) ^ (h + 1) • y = 0 := by
    have := Nat.find_spec hex; rw [hh] at this; exact this
  have hmin : ¬ ∀ y ∈ N, (TT) ^ h • y = 0 := Nat.find_min hex (by omega)
  obtain ⟨x, hxN, hx⟩ : ∃ x ∈ N, (TT) ^ h • x ≠ 0 := by
    by_contra hc
    apply hmin
    intro y hy
    by_contra hy'
    exact hc ⟨y, hy, hy'⟩
  refine ⟨x, le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hxN)⟩
  have hw : (TT) ^ h • x ∈ S :=
    (memS _).mpr ⟨N.smul_mem _ hxN, by rw [← mul_smul, ← pow_succ']; exact hspec x hxN⟩
  obtain ⟨c2, hc2⟩ := hv ⟨_, hw⟩
  have e2 : c2 • (v : Fin a → TruncK K' n) = (TT) ^ h • x := by
    rw [← Submodule.coe_smul_of_tower, hc2]
  have hc2ne : c2 ≠ 0 := by
    rintro rfl; apply hx; rw [← e2, zero_smul]
  have key : ∀ m : ℕ, ∀ y ∈ N, (TT) ^ m • y = 0 → y ∈ Submodule.span (TruncK K' n) {x} := by
    intro m
    induction m with
    | zero => intro y _ hy; rw [pow_zero, one_smul] at hy; rw [hy]; exact Submodule.zero_mem _
    | succ m ih =>
      intro y hy h0
      by_cases hz : (TT) ^ m • y = 0
      · exact ih y hy hz
      have hmh : m ≤ h := by
        by_contra hlt
        apply hz
        rw [← Nat.sub_add_cancel (not_le.mp hlt : h + 1 ≤ m), pow_add, mul_smul, hspec y hy, smul_zero]
      have hz' : (TT) ^ m • y ∈ S :=
        (memS _).mpr ⟨N.smul_mem _ hy, by rw [← mul_smul, ← pow_succ']; exact h0⟩
      obtain ⟨c1, hc1⟩ := hv ⟨_, hz'⟩
      have e1 : c1 • (v : Fin a → TruncK K' n) = (TT) ^ m • y := by
        rw [← Submodule.coe_smul_of_tower, hc1]
      have hy'N : y - (c1 / c2) • ((TT) ^ (h - m) • x) ∈ N :=
        N.sub_mem hy (N.smul_of_tower_mem _ (N.smul_mem _ hxN))
      have hy' : (TT) ^ m • (y - (c1 / c2) • ((TT) ^ (h - m) • x)) = 0 := by
        rw [smul_sub, smul_comm ((TT) ^ m) (c1 / c2), ← mul_smul, ← pow_add, Nat.add_sub_cancel' hmh,
          ← e1, ← e2, smul_smul, div_mul_cancel₀ _ hc2ne, sub_self]
      have hmem := ih _ hy'N hy'
      have hyeq : y = (y - (c1 / c2) • ((TT) ^ (h - m) • x)) + (c1 / c2) • ((TT) ^ (h - m) • x) := by
        rw [sub_add_cancel]
      rw [hyeq]
      exact Submodule.add_mem _ hmem (Submodule.smul_of_tower_mem _ _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
  intro y hy
  exact key (h + 1) y hy (hspec y hy)

end Cyc

section KerD
variable {K' : Type} [Field K'] {n : ℕ}

local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

lemma mul_eq_inv_mul {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (hP : IsUnit P.det) :
    Φ * Q = P⁻¹ * (P * Φ * Q) := by
  rw [Matrix.mul_assoc P, ← Matrix.mul_assoc P⁻¹, nonsing_inv_mul _ hP, Matrix.one_mul]

lemma ker_lower {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hk : ∀ i, k i ≤ n) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) :
    ∑ i, k i ≤ Module.finrank K' ↥(LinearMap.ker (Matrix.toLin' Φ)) := by
  classical
  let f : ∀ i, Fin (k i) → Fin n := fun i j => ⟨n - 1 - j, by have := hk i; have := j.2; omega⟩
  let v : ∀ i, Fin (k i) → TruncK K' n := fun i => (fun l : Fin n => (TT) ^ (l : ℕ)) ∘ f i
  have hv : ∀ i, LinearIndependent K' (v i) := by
    intro i
    have hinj : Function.Injective (f i) := by
      intro j j' hjj
      simp only [f, Fin.mk.injEq] at hjj
      have := hk i
      have := j.2
      have := j'.2
      ext; omega
    exact tt_linIndep.comp (f i) hinj
  have hS := Pi.linearIndependent_single v hv
  have hmem : ∀ s : (Σ i, Fin (k i)),
      Q *ᵥ Pi.single s.1 (v s.1 s.2) ∈ LinearMap.ker (Matrix.toLin' Φ) := by
    rintro ⟨i, j⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, mul_eq_inv_mul Φ P Q hP, hD,
      ← mulVec_mulVec]
    have h0 : diagonal (fun i => (TT) ^ k i) *ᵥ Pi.single (M := fun _ => TruncK K' n) i (v i j) = 0 := by
      funext l
      rw [mulVec_diagonal]
      by_cases hl : l = i
      · subst hl
        simp only [Pi.single_eq_same, v, f, Function.comp_apply, Pi.zero_apply]
        rw [← pow_add]
        exact tt_pow_ge (by have := j.2; omega)
      · simp [hl]
    rw [h0, mulVec_zero]
  have hker : LinearMap.ker ((Matrix.toLin' Q).restrictScalars K') = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z1 z2 hz
    simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at hz
    have := congrArg (fun z => Q⁻¹ *ᵥ z) hz
    simpa only [mulVec_mulVec, nonsing_inv_mul _ hQ, one_mulVec] using this
  have hw : LinearIndependent K' (fun s : (Σ i, Fin (k i)) => Q *ᵥ Pi.single s.1 (v s.1 s.2)) :=
    hS.map' ((Matrix.toLin' Q).restrictScalars K') hker
  have hw' : LinearIndependent K' (fun s : (Σ i, Fin (k i)) =>
      (⟨_, hmem s⟩ : ↥(LinearMap.ker (Matrix.toLin' Φ)))) :=
    LinearIndependent.of_comp ((LinearMap.ker (Matrix.toLin' Φ)).subtype.restrictScalars K') hw
  have := hw'.fintype_card_le_finrank
  simpa [Fintype.card_sigma, Fintype.card_fin] using this

lemma ker_kill {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) (m : ℕ) (hm : ∀ i, k i ≤ m)
    (y : Fin a → TruncK K' n) (hy : y ∈ LinearMap.ker (Matrix.toLin' Φ)) : (TT) ^ m • y = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy
  have hz : diagonal (fun i => (TT) ^ k i) *ᵥ (Q⁻¹ *ᵥ y) = 0 := by
    rw [← hD, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one,
      ← mulVec_mulVec, hy, mulVec_zero]
  have hz' : (TT) ^ m • (Q⁻¹ *ᵥ y) = 0 := by
    funext i
    have := congrFun hz i
    rw [mulVec_diagonal, Pi.zero_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← Nat.sub_add_cancel (hm i), pow_add, mul_assoc, this, mul_zero]
  have hy' : y = Q *ᵥ (Q⁻¹ *ᵥ y) := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hQ, one_mulVec]
  rw [hy', ← mulVec_smul, hz', mulVec_zero]

lemma det_eq {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) :
    P.det * Φ.det * Q.det = (TT) ^ (∑ i, k i) := by
  rw [← det_mul, ← det_mul, hD, det_diagonal, Finset.prod_pow_eq_pow_sum]

lemma adj_mem {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) (I : Ideal (TruncK K' n))
    (hI : ∀ i j, adjugate Φ i j ∈ I) (i0 : Fin a) :
    (TT) ^ (∑ j ∈ Finset.univ.erase i0, k j) ∈ I := by
  classical
  have h1 : adjugate (P * Φ * Q) = adjugate Q * (adjugate Φ * adjugate P) := by
    rw [adjugate_mul_distrib, adjugate_mul_distrib]
  have h2 : ∀ i j, adjugate (P * Φ * Q) i j ∈ I := by
    intro i j
    rw [h1, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => I.mul_mem_left _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => I.mul_mem_right _ (hI l m)
  have h3 := h2 i0 i0
  rw [hD, adjugate_diagonal, diagonal_apply_eq, Finset.prod_pow_eq_pow_sum] at h3
  exact h3

end KerD
end residueMatrixData

open residueMatrixData in

theorem residue_module_structure : RESModule := by
  intro K' _ n a C Φ N hC hN hdim
  classical
  obtain ⟨P, Q, hP, hQ, d, hd⟩ := exists_diag (trunc_total (K' := K') (n := n)) a Φ
  choose k hk u hu hdu using fun i => trunc_normal (K' := K') (n := n) (d i)
  set T : TruncK K' n := Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X with hT
  let w : Fin a → TruncK K' n := fun i => (((hu i).unit⁻¹ : (TruncK K' n)ˣ) : TruncK K' n)
  have hP2 : IsUnit (diagonal w * P).det := by
    rw [det_mul, det_diagonal]
    have : ∏ i, w i = ((∏ i, (hu i).unit⁻¹ : (TruncK K' n)ˣ) : TruncK K' n) := by
      rw [Units.coe_prod]
    rw [this]
    exact (Units.isUnit _).mul hP
  have hD2 : diagonal w * P * Φ * Q = diagonal (fun i => T ^ k i) := by
    rw [show diagonal w * P * Φ * Q = diagonal w * (P * Φ * Q) by simp only [Matrix.mul_assoc], hd,
      diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [w]
    rw [hdu i, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  have hkerL := ker_lower Φ _ Q k hk hP2 hQ hD2
  have hsplit := finrank_split (LinearMap.ker (Matrix.toLin' Φ)) N hN
  refine ⟨fun hTor => ?_, fun ha hsoc => ?_⟩
  · have hNb := eq_bot_of_noTorsion N hTor
    refine ⟨hNb, fun hdet => ?_⟩
    have h0 : Module.finrank K' ↥N = 0 := by rw [hNb]; exact Module.finrank_zero_of_subsingleton
    have hsum : ∑ i, k i ≤ C := by omega
    have hmem : T ^ (∑ i, k i) ∈ Ideal.span {T ^ (C + 1)} := by
      rw [← det_eq Φ _ Q k hD2]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdet)
    exact tt_pow_notMem hsum hC hmem
  · obtain ⟨x, hx⟩ := cyclic_of_socle N hsoc
    refine ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
    by_contra hcon
    have hall : ∀ i j, adjugate Φ i j ∈ Ideal.span {T ^ (C + 1)} := by
      intro i j
      rw [adjugate_fin_succ_eq_det_submatrix]
      apply Ideal.mul_mem_left
      by_contra hm
      exact hcon ⟨j, i, a', rfl, by simpa using hm⟩
    have hmem := adj_mem Φ _ Q k hD2 _ hall i0
    have hxN : x ∈ N := by rw [hx]; exact Submodule.mem_span_singleton_self x
    have hNle : Module.finrank K' ↥N ≤ k i0 := by
      rw [hx]
      exact finrank_span_le x (ker_kill Φ _ Q k hP2 hQ hD2 (k i0) (fun i => hi0 i (Finset.mem_univ i)) x
        (hN hxN))
    have hsum := Finset.add_sum_erase Finset.univ k (Finset.mem_univ i0)
    have hle : ∑ j ∈ Finset.univ.erase i0, k j ≤ C := by omega
    exact tt_pow_notMem hle hC hmem

end
end Formalism.CyclotomicNorms

import Formalism.CyclotomicNorms.StatementA

open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

namespace CentralScalarSequence

variable {G : Type} [Group G]

def insN (i : ℕ) (a : G) (y : ℕ → G) : ℕ → G :=
  fun k => if k < i then y k else if k = i then a else y (k - 1)

def contrN (j : ℕ) (y : ℕ → G) : ℕ → G :=
  fun k => if k < j then y k else if k = j then y k * y (k + 1) else y (k + 1)

def extN {m : ℕ} (x : Fin m → G) : ℕ → G := fun k => if h : k < m then x ⟨k, h⟩ else 1

lemma extN_agree {m : ℕ} (x : Fin m → G) : ∀ k : Fin m, x k = extN x k := by
  intro k; simp [extN, k.isLt]

lemma ins_agree {m : ℕ} (i : Fin (m + 1)) (a : G) (x : Fin m → G) (y : ℕ → G)
    (hx : ∀ k : Fin m, x k = y k) :
    ∀ k : Fin (m + 1), Fin.insertNth (α := fun _ => G) i a x k = insN i a y k := by
  intro k
  rcases lt_trichotomy k i with h | h | h
  · rw [Fin.insertNth_apply_below h, eq_rec_constant, hx]
    have h' : (k : ℕ) < i := h
    simp [insN, h']
  · subst h; simp [insN]
  · rw [Fin.insertNth_apply_above h, eq_rec_constant, hx]
    have h' : (i : ℕ) < k := h
    simp [insN, not_lt.mpr h'.le, h'.ne']

lemma contr_agree {m : ℕ} (j : Fin (m + 1)) (x : Fin (m + 1) → G) (y : ℕ → G)
    (hx : ∀ k : Fin (m + 1), x k = y k) :
    ∀ k : Fin m, Fin.contractNth j (· * ·) x k = contrN j y k := by
  intro k
  simp only [Fin.contractNth, contrN, hx, Fin.val_castSucc, Fin.val_succ]

section seq

variable (a : G) (y : ℕ → G)

lemma seq_a (M j : ℕ) (h : j < M) : contrN j (insN (M + 1) a y) = insN M a (contrN j y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)

lemma seq_b (hz : ∀ g, a * g = g * a) (M : ℕ) :
    contrN M (insN (M + 1) a y) = contrN M (insN M a y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega) | (subst_vars; exact (hz _).symm)

lemma seq_c (M i : ℕ) (h : i ≤ M) : contrN (M + 1) (insN i a y) = insN i a (contrN M y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)

lemma seq_d (i : ℕ) : insN (i + 1) a y 0 = y 0 := by simp [insN]

lemma seq_e (i : ℕ) : (fun k => insN (i + 1) a y (k + 1)) = insN i a (fun k => y (k + 1)) := by
  funext k
  simp only [insN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)

lemma seq_f : insN 0 a y 0 = a := by simp [insN]

lemma seq_g : (fun k => insN 0 a y (k + 1)) = y := by
  funext k; simp [insN]

lemma seq_h (n k : ℕ) (hk : k < n + 1) : contrN (n + 1) (insN (n + 1) a y) k = y k := by
  simp [insN, contrN, hk]

end seq

lemma abstract {W : Type} [AddCommGroup W] (T S : ℕ → ℕ → W)
    (h1 : ∀ M j, j < M → T (M + 1) j = - S M j) (h2 : ∀ M, T (M + 1) M = - T M M)
    (h3 : ∀ M i, i ≤ M → T i (M + 1) = - S i M) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) +
      (∑ i ∈ range N, ∑ j ∈ range N, S i j) = T N N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have eT : ∑ i ∈ range (N + 1 + 1), ∑ j ∈ range (N + 1 + 1), T i j =
        (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) + (∑ i ∈ range (N + 1), T i (N + 1))
        + ((∑ j ∈ range N, T (N + 1) j) + T (N + 1) N) + T (N + 1) (N + 1) := by
      rw [sum_range_succ _ (N + 1)]
      simp only [sum_range_succ _ (N + 1), sum_add_distrib]
      rw [← sum_range_succ (fun j => T (N + 1) j) N]
      abel
    have eS : ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), S i j =
        (∑ i ∈ range N, ∑ j ∈ range N, S i j) + (∑ i ∈ range N, S i N) +
        (∑ j ∈ range N, S N j) + S N N := by
      rw [sum_range_succ _ N]
      simp only [sum_range_succ _ N, sum_add_distrib]
      abel
    have e1 : ∑ j ∈ range N, T (N + 1) j = - ∑ j ∈ range N, S N j := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun j hj => h1 N j (mem_range.mp hj)
    have e2 : ∑ i ∈ range (N + 1), T i (N + 1) = - ((∑ i ∈ range N, S i N) + S N N) := by
      rw [← sum_range_succ (fun i => S i N) N, ← sum_neg_distrib]
      exact sum_congr rfl fun i hi => h3 N i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    rw [eT, eS, e1, e2, h2 N]
    have ih' := eq_sub_of_add_eq ih
    rw [ih']
    abel

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

lemma sgn_succ (k : ℕ) : (-1 : R) ^ (k + 1) = - (-1 : R) ^ k := by
  rw [pow_succ, mul_neg_one]

lemma sgn_diag (i : ℕ) : (-1 : R) ^ (i + (i + 1)) = -1 := by
  rw [show i + (i + 1) = 2 * i + 1 by ring, pow_succ, pow_mul]; simp

lemma nat_identity (ρ : Representation R G W) (z : G) (hz : ∀ g, z * g = g * z) (n : ℕ)
    (φ : (ℕ → G) → W) (hφ : ∀ u v : ℕ → G, (∀ k < n + 1, u k = v k) → φ u = φ v) (y : ℕ → G)
    (hcoc : ∀ i < n + 2, ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1))) +
      ∑ j ∈ range (n + 2), (-1 : R) ^ (j + 1) • φ (contrN j (insN i z y)) = 0) :
    ρ (y 0) (∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (fun k => y (k + 1)))) +
      ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
        ∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (contrN j y))
      = ρ z (φ y) - φ y := by
  have h0 : (∑ i ∈ range (n + 2), (-1 : R) ^ i • ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1))))
      + ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
          (-1 : R) ^ (i + (j + 1)) • φ (contrN j (insN i z y)) = 0 := by
    rw [← sum_add_distrib]
    refine sum_eq_zero fun i hi => ?_
    have := congrArg (fun w => (-1 : R) ^ i • w) (hcoc i (mem_range.mp hi))
    simp only [smul_add, smul_sum, smul_smul, ← pow_add, smul_zero] at this
    exact this
  have hA : ∑ i ∈ range (n + 2), (-1 : R) ^ i • ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1)))
      = ρ z (φ y) - ρ (y 0) (∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (fun k => y (k + 1)))) := by
    rw [sum_range_succ']
    simp only [seq_d, seq_e, seq_f, seq_g, pow_zero, one_smul, map_sum, map_smul, sgn_succ,
      neg_smul, sum_neg_distrib]
    abel
  have hK := abstract (fun i j => (-1 : R) ^ (i + (j + 1)) • φ (contrN j (insN i z y)))
      (fun i j => (-1 : R) ^ (i + (j + 1)) • φ (insN i z (contrN j y)))
      (fun M j h => by
        rw [seq_a z y M j h, show M + 1 + (j + 1) = M + (j + 1) + 1 by omega, sgn_succ, neg_smul])
      (fun M => by
        rw [seq_b z y hz M, show M + 1 + (M + 1) = M + (M + 1) + 1 by omega, sgn_succ, neg_smul])
      (fun M i h => by
        rw [seq_c z y M i h, show i + (M + 1 + 1) = i + (M + 1) + 1 by omega, sgn_succ, neg_smul])
      (n + 1)
  rw [sgn_diag, neg_one_smul, hφ _ y (seq_h z y n)] at hK
  have hB : ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
        ∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (contrN j y)) =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (-1 : R) ^ (i + (j + 1)) • φ (insN i z (contrN j y)) := by
    simp only [smul_sum, smul_smul, ← pow_add]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [show j + 1 + i = i + (j + 1) by omega]
  rw [hA, eq_sub_of_add_eq hK] at h0
  rw [hB]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h0]
  abel

def prism (R : Type) [CommRing R] [Module R W] {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W)
    (x : Fin n → G) : W :=
  ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • f (Fin.insertNth (α := fun _ => G) i z x)

lemma prism_eq {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W) (x : Fin n → G) (v : ℕ → G)
    (hx : ∀ k : Fin n, x k = v k) :
    prism R z f x = ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z v k) := by
  unfold prism
  rw [← Fin.sum_univ_eq_sum_range (fun i => (-1 : R) ^ i • f (fun k => insN i z v k)) (n + 1)]
  refine sum_congr rfl fun i _ => ?_
  congr 2
  funext k
  exact ins_agree i z x v hx k

lemma prism_continuous [TopologicalSpace G] [TopologicalSpace W] [DiscreteTopology W] {n : ℕ}
    (z : G) (f : (Fin (n + 1) → G) → W) (hf : Continuous f) : Continuous (prism R z f) := by
  have hV : Continuous fun x : Fin n → G => fun i : Fin (n + 1) =>
      f (Fin.insertNth (α := fun _ => G) i z x) :=
    continuous_pi fun i => hf.comp (continuous_const.finInsertNth i continuous_id)
  exact (continuous_of_discreteTopology
    (f := fun v : Fin (n + 1) → W => ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • v i)).comp hV

end CentralScalarSequence

open CentralScalarSequence in
theorem central_scalar_holds : CentralScalar := by
  intro G R W _ _ _ _ _ _ _ ρ z c hz hc hρz
  have hzc : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  obtain ⟨u, hu⟩ := hc
  refine ⟨?_, ?_⟩
  · intro w hw
    have h1 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← hρz, hw, sub_self]
    calc w = ((↑u⁻¹ : R) * ↑u) • w := by simp
      _ = (↑u⁻¹ : R) • ((c - 1) • w) := by rw [mul_smul, hu]
      _ = 0 := by rw [h1, smul_zero]
  · intro n f hf hcoc
    refine ⟨fun x => (↑u⁻¹ : R) • prism R z f x,
      (continuous_of_discreteTopology (f := fun w : W => (↑u⁻¹ : R) • w)).comp
        (prism_continuous z f hf), ?_⟩
    funext g
    have key : coboundary ρ n (prism R z f) g = (c - 1) • f g := by
      set y := extN g with hy
      have hg := extN_agree g
      rw [← hy] at hg
      simp only [coboundary]
      rw [prism_eq z f (fun i => g i.succ) (fun k => y (k + 1)) (fun k => by simp [hg])]
      have hsum : ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • prism R z f (Fin.contractNth j (· * ·) g)
          = ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
            ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z (contrN j y) k) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1) •
          ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z (contrN j y) k)) (n + 1)]
        refine sum_congr rfl fun j _ => ?_
        rw [prism_eq z f _ (contrN j y) (contr_agree j g y hg)]
      rw [hsum]
      rw [show f g = f (fun k => y k) from congrArg f (funext hg), sub_smul, one_smul, ← hρz,
        hg 0, Fin.val_zero]
      refine nat_identity ρ z hzc n (fun v => f (fun k => v k)) ?_ y ?_
      · intro u v huv
        exact congrArg f (funext fun k => huv k k.isLt)
      · intro i hi
        have := congrFun hcoc (fun k : Fin (n + 2) => insN i z y k)
        simp only [coboundary, Pi.zero_apply] at this
        have hsum : ∑ j : Fin (n + 2), (-1 : R) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) (fun k : Fin (n + 2) => insN i z y k)) =
            ∑ j ∈ range (n + 2), (-1 : R) ^ (j + 1) • f (fun k => contrN j (insN i z y) k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1) •
            f (fun k => contrN j (insN i z y) k)) (n + 2)]
          refine sum_congr rfl fun j _ => ?_
          rw [show Fin.contractNth j (· * ·) (fun k : Fin (n + 2) => insN i z y k) =
            fun k : Fin (n + 1) => contrN j (insN i z y) k from
              funext (contr_agree j _ _ fun _ => rfl)]
        rw [hsum] at this
        simpa using this
    have lin : coboundary ρ n (fun x => (↑u⁻¹ : R) • prism R z f x) g =
        (↑u⁻¹ : R) • coboundary ρ n (prism R z f) g := by
      simp only [coboundary, map_smul, smul_add, smul_sum]
      congr 1
      exact sum_congr rfl fun j _ => smul_comm _ _ _
    rw [lin, key, ← hu, smul_smul, Units.inv_mul, one_smul]

end Formalism.CyclotomicNorms

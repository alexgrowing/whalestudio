import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DiagScalar₂
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

theorem mul_p (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    (∑ i, e i • p i) * p j = e j • p j := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, (hp.1.idem j).eq]
  · intro b _ hb; rw [smul_mul_assoc, hp.1.ortho hb, smul_zero]
  · simp

theorem p_mul (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    p j * (∑ i, e i • p i) = e j • p j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, (hp.1.idem j).eq]
  · intro b _ hb; rw [mul_smul_comm, hp.1.ortho (Ne.symm hb), smul_zero]
  · simp

theorem vec_of (p : Fin n → Mat C N) (hp : Sys p) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : p i *ᵥ v = v := by
  have h1 : (∑ k, p k) *ᵥ v = v := by rw [hp.1.complete]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h1
  · exact h1
  · intro b _ hb; exact hv b hb
  · simp

theorem X_vec (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : (∑ k, e k • p k) *ᵥ v = e i • v := by
  have h := vec_of p hp i v hv
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, mul_p p hp e i, Matrix.smul_mulVec, h]

theorem root_of_eig (Y : Mat C N) (μ : C) (v : Fin N → C) (hv : v ≠ 0) (h : Y *ᵥ v = μ • v) :
    Y.charpoly.IsRoot μ := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, h, Matrix.scalar_apply]
  ext k; simp [Matrix.mulVec_diagonal]

theorem deg_shift (x : Mat C N) (c : C) (h : Deg n x) : Deg n (x + algebraMap C (Mat C N) c) := by
  obtain ⟨q, hq, hd, ha⟩ := h
  refine ⟨Polynomial.taylor (-c) q, ?_, ?_, ?_⟩
  · rwa [Ne, Polynomial.taylor_eq_zero]
  · rwa [Polynomial.natDegree_taylor]
  · rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simp [ha]

theorem alg_vec (c : C) (v : Fin N → C) : (algebraMap C (Mat C N) c) *ᵥ v = c • v := by
  rw [Matrix.algebraMap_eq_diagonal]; ext k; simp [Matrix.mulVec_diagonal]

end LateralTheory.DivDb.DiagScalar₂

namespace LateralTheory.DivDb
open DiagScalar₂ in
theorem DiagScalar_of (hC : CycleCount) : DiagScalar := by
  intro C _ _ _ N n p e Y hp he hY hD i
  classical
  have : Infinite C := Infinite.of_injective _ Nat.cast_injective
  set X := ∑ i, e i • p i with hX
  set R := Y.charpoly.roots.toFinset with hR
  set B : Finset C := insert 0 ((R ×ˢ R ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image
    (fun t => (e t.2.2.2 - e t.2.2.1) / (t.1 - t.2.1))) with hB
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset B
  have hs0 : s ≠ 0 := fun h => hs (h ▸ Finset.mem_insert_self _ _)
  set M := s • Y + X with hM
  obtain ⟨c', hc'⟩ := Infinite.exists_notMem_finset ((-M).charpoly.roots.toFinset)
  set y := M + algebraMap C (Mat C N) c' with hy
  have hunit : IsUnit y := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0; apply hc'
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot,
      Matrix.eval_charpoly]
    convert h0 using 2
    rw [hy, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, sub_neg_eq_add, add_comm]; rfl
  have hcomm : ∀ j, y * p j = p ((1 : Equiv.Perm (Fin n)) j) * y := by
    intro j
    rw [Equiv.Perm.one_apply, hy, hM, add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, hY j,
      hX, mul_p p hp e j, p_mul p hp e j, Algebra.commutes]
  have hdeg : Deg n y := deg_shift _ c' (hD s)
  have key : ∀ (i : Fin n) (l : C) (v : Fin N → C), v ≠ 0 → y *ᵥ v = l • v →
      (∀ k, ¬ i = k → p k *ᵥ v = 0) → ∃ μ ∈ R, s * μ + e i = l - c' := by
    intro i l v hv hyv hpv
    have hXv := X_vec p hp e i v (fun k hk => hpv k (Ne.symm hk))
    have h1 : y *ᵥ v = s • (Y *ᵥ v) + e i • v + c' • v := by
      rw [hy, hM, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hX, hXv, alg_vec]
    rw [h1] at hyv
    have h2 : s • (Y *ᵥ v) = (l - c' - e i) • v := by rw [sub_smul, sub_smul, ← hyv]; abel
    refine ⟨s⁻¹ * (l - c' - e i), ?_, by field_simp; ring⟩
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    apply root_of_eig Y _ v hv
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hdisj : Disj y 1 p := by
    intro i j hij l v w hv hw hyv hyw hpv hpw
    simp only [Equiv.Perm.sameCycle_one] at hij hpv hpw
    obtain ⟨μ, hμ, h1⟩ := key i l v hv hyv hpv
    obtain ⟨μ', hμ', h2⟩ := key j l w hw hyw hpw
    have hne : e i ≠ e j := he.ne hij
    have hμμ : μ - μ' ≠ 0 := by
      intro h; apply hne
      have : μ = μ' := sub_eq_zero.mp h
      subst this; linear_combination h1 - h2
    apply hs
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_image]
    refine ⟨(μ, μ', i, j), by simp [hμ, hμ'], ?_⟩
    show (e j - e i) / (μ - μ') = s
    rw [div_eq_iff hμμ]; linear_combination h2 - h1
  obtain ⟨_, hfix⟩ := hC C N n p y 1 hp hunit hcomm hdeg hdisj
  obtain ⟨c, hc⟩ := hfix i rfl
  refine ⟨s⁻¹ * (c - e i - c'), ?_⟩
  have h4 : y * p i = s • (Y * p i) + e i • p i + c' • p i := by
    rw [hy, hM, add_mul, add_mul, smul_mul_assoc, hX, mul_p p hp e i, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [h4] at hc
  have h3 : s • (Y * p i) = (c - e i - c') • p i := by rw [sub_smul, sub_smul, ← hc]; abel
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end LateralTheory.DivDb

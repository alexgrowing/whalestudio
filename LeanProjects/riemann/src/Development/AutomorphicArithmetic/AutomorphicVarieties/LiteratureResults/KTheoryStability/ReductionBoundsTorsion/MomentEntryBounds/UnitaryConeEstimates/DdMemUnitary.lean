import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.KB.MomentRationality.Cz.Red

def dd {R : Type*} [CommRing R] (N : ℕ) (u : R) : Matrix (Fin N) (Fin N) R :=
  diagonal fun i => if (i : ℕ) = 0 then u else 1

theorem dd_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (u : R) :
    (dd N u).map f = dd N (f u) := by
  unfold dd
  rw [diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_mul {R : Type*} [CommRing R] (N : ℕ) (u v : R) : dd N u * dd N v = dd N (u * v) := by
  unfold dd
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dd_one {R : Type*} [CommRing R] (N : ℕ) : dd N (1 : R) = 1 := by
  unfold dd
  simp

theorem det_dd {R : Type*} [CommRing R] {N : ℕ} (hN : 1 ≤ N) (u : R) : (dd N u).det = u := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  unfold dd
  rw [det_diagonal, Fin.prod_univ_succ]
  simp [Fin.val_succ]

theorem star_dd (N : ℕ) (c : ℂ) : star (dd N c) = dd N (star c) := by
  unfold dd
  rw [star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dd_mem_unitary (N : ℕ) {c : ℂ} (hc : c ∈ unitary ℂ) : dd N c ∈ unitaryGroup (Fin N) ℂ := by
  rw [mem_unitaryGroup_iff, star_dd, dd_mul, Unitary.mul_star_self_of_mem hc, dd_one]

theorem norm_dd_apply {N : ℕ} {c : ℂ} (hc : ‖c‖ = 1) (j : Fin N) :
    ‖(if (j : ℕ) = 0 then c else 1 : ℂ)‖ = 1 := by
  split_ifs <;> simp [hc]

def ddGL {R : Type*} [CommRing R] (N : ℕ) (u : Rˣ) : GL (Fin N) R :=
  ⟨dd N (u : R), dd N ((u⁻¹ : Rˣ) : R), by rw [dd_mul, Units.mul_inv, dd_one],
    by rw [dd_mul, Units.inv_mul, dd_one]⟩

theorem exists_root {N : ℕ} (hN : N ≠ 0) {d : ℂ} (hd : d ≠ 0) : ∃ z : ℂ, z ≠ 0 ∧ z ^ N * d = 1 := by
  refine ⟨d⁻¹ ^ ((N : ℂ)⁻¹), ?_, ?_⟩
  · intro h
    have := Complex.cpow_nat_inv_pow d⁻¹ hN
    rw [h, zero_pow hN] at this
    exact inv_ne_zero hd this.symm
  · rw [Complex.cpow_nat_inv_pow _ hN, inv_mul_cancel₀ hd]

theorem cancel_left {N : ℕ} {A X B : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {z c : ℂ} (hz : z ≠ 0)
    (h : (z • A) * X = c • (A * B)) : X = (z⁻¹ * c) • B := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have h2 : A * (z • X) = A * (c • B) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, h]
  have h3 : z • X = c • B := by
    have := congrArg (fun Y => A⁻¹ * Y) h2
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu] using this
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hz, one_smul]

open NumberField in
theorem units_fin {L : Type*} [Field L] [NumberField L] (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (𝓞 L)ˣ, ∀ u : (𝓞 L)ˣ, ∃ v : (𝓞 L)ˣ, ∃ u0 ∈ S, u = v ^ N * u0 := by
  classical
  let f : Units.torsion L × (Fin (Units.rank L) → Fin N) → (𝓞 L)ˣ :=
    fun p => (p.1 : (𝓞 L)ˣ) * ∏ i, Units.fundSystem L i ^ ((p.2 i : ℕ) : ℤ)
  refine ⟨(Set.finite_range f).toFinset, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := Units.exist_unique_eq_mul_prod L u
  have h1 : ∀ i, 0 ≤ e i % N := fun i => Int.emod_nonneg (e i) (by omega)
  have h2 : ∀ i, e i % N < N := fun i => Int.emod_lt_of_pos (e i) (by omega)
  refine ⟨∏ i, Units.fundSystem L i ^ (e i / N), f (ζ, fun i => ⟨(e i % N).toNat, by
    have := h2 i; have := h1 i; omega⟩), by simp, ?_⟩
  have hsplit : ∀ i, Units.fundSystem L i ^ e i =
      (Units.fundSystem L i ^ (e i / N)) ^ N * Units.fundSystem L i ^ (((e i % N).toNat : ℕ) : ℤ) := by
    intro i
    rw [Int.toNat_of_nonneg (h1 i), ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
    congr 1
    linarith [Int.mul_ediv_add_emod (e i) N]
  rw [hu]
  simp only [f]
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib, Finset.prod_pow]
  ac_rfl

end PositivityTheory.KB.MomentRationality.Cz.Red

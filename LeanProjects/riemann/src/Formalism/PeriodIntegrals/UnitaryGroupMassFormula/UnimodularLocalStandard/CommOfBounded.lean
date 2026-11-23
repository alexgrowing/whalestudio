import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.IsKTheta

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

def IsKv (b : ℤ) (d : ℕ) (lam : ℂ) (v : m → ℂ) : Prop := ∀ i, IsK b d (v i / lam)

lemma cmL_omega1 : (cmL a b d ha hd lam hlam).ω₁ = lam * a := rfl
lemma cmL_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := rfl

lemma mem_stdLat_iff (L : PeriodPair) (v : m → ℂ) : v ∈ stdLat L m ↔ ∀ i, v i ∈ L.lattice := by
  simp only [PI.ULS.stdLat, AddSubgroup.mem_pi, Set.mem_univ, forall_const,
    Submodule.mem_toAddSubgroup]

private theorem mul_div_cancel_left_of_ne_zero {w : ℂ} (hw : w ≠ 0) (x : ℂ) : w * x / w = x := by
  rw [mul_comm, mul_div_assoc, div_self hw, mul_one]

private theorem mem_cmL_lattice_iff (z : ℂ) :
    z ∈ (PI.ULS.cmL a b d ha hd lam hlam).lattice ↔
      ∃ p q : ℤ, z = lam * ((p : ℂ) * a + q * PI.ULS.cmTheta b d) := by
  rw [lattice_iff]
  simp only [cmL_omega1, cmL_omega2, Complex.real_smul, Complex.ofReal_intCast]
  constructor
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩

lemma isKv_of_mem {s : m → ℂ} (hs : s ∈ stdLat (cmL a b d ha hd lam hlam) m) : IsKv b d lam s := by
  intro i
  obtain ⟨p, q, hpq⟩ := (mem_cmL_lattice_iff _).1 ((mem_stdLat_iff _ s).1 hs i)
  refine ⟨p * (a : ℤ), q, 1, one_ne_zero, ?_⟩
  rw [hpq, mul_div_cancel_left_of_ne_zero hlam]
  push_cast
  ring

private theorem natCast_smul_eq_nsmul (N : ℕ) (y : m → ℂ) : (N : ℂ) • y = N • y := by
  exact Nat.cast_smul_eq_nsmul ℂ N y

private theorem nsmul_apply_eq_natCast_mul (N : ℕ) (v : m → ℂ) (i : m) : (N • v) i = (N : ℂ) * v i := by
  rw [← natCast_smul_eq_nsmul, Pi.smul_apply, smul_eq_mul]

lemma exists_nsmul_mem {v : m → ℂ} (h : IsKv b d lam v) :
    ∃ N : ℕ, N ≠ 0 ∧ N • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose p q r hr hpq using h
  have hself : ∀ z : ℤ, z ∣ (z.natAbs : ℤ) := fun _ => Int.dvd_natAbs.mpr dvd_rfl
  obtain ⟨M, hM0, hMdvd⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ i, r i ∣ (M : ℤ) := by
    refine ⟨∏ j, (r j).natAbs, Finset.prod_ne_zero_iff.mpr fun j _ => Int.natAbs_ne_zero.mpr (hr j),
      fun i => (hself (r i)).trans ?_⟩
    have hi : (r i).natAbs ∣ ∏ j, (r j).natAbs :=
      Finset.dvd_prod_of_mem (fun j => (r j).natAbs) (Finset.mem_univ i)
    exact Int.natCast_dvd_natCast.mpr hi
  refine ⟨a * M, mul_ne_zero ha.ne' hM0, ?_⟩
  rw [mem_stdLat_iff]
  intro i
  obtain ⟨k, hk⟩ := hMdvd i
  have hk' : (M : ℂ) = (r i : ℂ) * k := by exact_mod_cast hk
  have e : v i = v i / lam * lam := (div_eq_iff hlam).mp rfl
  have hv : (r i : ℂ) * v i = lam * (p i + q i * PI.ULS.cmTheta b d) := by
    calc (r i : ℂ) * v i = (r i * (v i / lam)) * lam := by rw [mul_assoc, ← e]
      _ = (p i + q i * PI.ULS.cmTheta b d) * lam := by rw [hpq i]
      _ = lam * (p i + q i * PI.ULS.cmTheta b d) := mul_comm _ _
  rw [mem_cmL_lattice_iff]
  refine ⟨k * p i, a * k * q i, ?_⟩
  rw [nsmul_apply_eq_natCast_mul, Nat.cast_mul, hk']
  push_cast
  linear_combination ((a : ℂ) * k) * hv

lemma isKv_of_nsmul {v : m → ℂ} {N : ℕ} (hN : N ≠ 0) (h : IsKv b d lam (N • v)) : IsKv b d lam v := by
  intro i
  obtain ⟨p, q, r, hr, h'⟩ := h i
  refine ⟨p, q, r * N, mul_ne_zero hr (by exact_mod_cast hN), ?_⟩
  rw [← h', nsmul_apply_eq_natCast_mul]
  push_cast
  ring

lemma isKv_sub {v w : m → ℂ} (hv : IsKv b d lam v) (hw : IsKv b d lam w) : IsKv b d lam (v - w) := by
  intro i
  rw [Pi.sub_apply, sub_div]
  exact isK_sub (hv i) (hw i)

lemma isKv_smul {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) {t : ℂ} {v : m → ℂ}
    (ht : IsK b d t) (hv : IsKv b d lam v) : IsKv b d lam (t • v) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  exact isK_mul hn ht (hv i)

lemma isKv_single {w : ℂ} (hw : IsK b d (w / lam)) (i : m) : IsKv b d lam (Pi.single i w) := by
  intro j
  rw [Pi.single_apply]
  split_ifs
  · exact hw
  · rw [zero_div]
    exact ⟨0, 0, 1, one_ne_zero, by simp⟩

def kappa (L : PeriodPair) (lam : ℂ) : ℂ := lam * conj lam * ((area L : ℝ) : ℂ)⁻¹

lemma kappa_conj (L : PeriodPair) (lam : ℂ) : conj (kappa L lam) = kappa L lam := by
  simp only [kappa]
  rw [map_mul, map_mul, map_inv₀, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma kappa_ne (L : PeriodPair) (hlam : lam ≠ 0) : kappa L lam ≠ 0 := by
  have harea : ((area L : ℝ) : ℂ) ≠ 0 := by
    rw [area_eq]
    exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (detD_ne L))
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  simp only [kappa]
  exact mul_ne_zero (mul_ne_zero hlam hc) (inv_ne_zero harea)

lemma stdH_kappa (L : PeriodPair) (hlam : lam ≠ 0) (x y : m → ℂ) :
    stdH L m x y = kappa L lam * ∑ i, (x i / lam) * conj (y i / lam) := by
  have hc : conj lam ≠ 0 := by rwa [Ne, map_eq_zero]
  have h1 : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  have h2 : conj lam * (conj lam)⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [stdH_apply]
  simp only [kappa]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_div₀]
  linear_combination (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹) * (conj lam * (conj lam)⁻¹)) * h1 +
    (-(x i * conj (y i) * ((area L : ℝ) : ℂ)⁻¹)) * h2

lemma isK_H {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) (L : PeriodPair) (hlam : lam ≠ 0)
    {x y : m → ℂ} (hx : IsKv b d lam x) (hy : IsKv b d lam y) :
    ∃ t, IsK b d t ∧ stdH L m x y = kappa L lam * t :=
  ⟨∑ i, (x i / lam) * conj (y i / lam),
    isK_sum hn _ _ fun i _ => isK_mul hn (hx i) (isK_conj (hy i)),
    stdH_kappa L hlam x y⟩

private theorem intCast_smul_eq_zsmul (p : ℤ) (y : m → ℂ) : (p : ℂ) • y = p • y := by
  exact Int.cast_smul_eq_zsmul ℂ p y

private theorem nsmul_intCast_smul_comm (N : ℕ) (p : ℤ) (y : m → ℂ) : N • ((p : ℂ) • y) = p • (N • y) := by
  rw [← natCast_smul_eq_nsmul N ((p : ℂ) • y), ← natCast_smul_eq_nsmul N y, smul_comm (N : ℂ) (p : ℂ) y,
    intCast_smul_eq_zsmul p ((N : ℂ) • y)]

private theorem nsmul_mem_of_dvd_of_nsmul_mem {S : AddSubgroup (m → ℂ)} {x : m → ℂ} {n N : ℕ} (hnN : n ∣ N)
    (hx : n • x ∈ S) : N • x ∈ S := by
  obtain ⟨k, rfl⟩ := hnN
  have e : (n * k) • x = k • (n • x) := by
    calc (n * k) • x = ((n * k : ℕ) : ℂ) • x := (natCast_smul_eq_nsmul _ _).symm
      _ = (k : ℂ) • (n : ℂ) • x := by rw [smul_smul, Nat.cast_mul, mul_comm]
      _ = k • n • x := by rw [natCast_smul_eq_nsmul, natCast_smul_eq_nsmul]
  rw [e]
  exact nsmul_mem hx k

lemma bounded_map (φ : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (h1 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₁)))
    (h2 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₂))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m,
      N • φ s ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose N1 hN1 hm1 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h1 i)
  choose N2 hN2 hm2 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h2 i)
  refine ⟨∏ j, N1 j * N2 j, Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero (hN1 j) (hN2 j), ?_⟩
  have hdvd : ∀ i, N1 i * N2 i ∣ ∏ j, N1 j * N2 j := fun i =>
    Finset.dvd_prod_of_mem (fun j => N1 j * N2 j) (Finset.mem_univ i)
  have k1 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_right (N1 i) (N2 i)).trans (hdvd i)) (hm1 i)
  have k2 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_left (N2 i) (N1 i)).trans (hdvd i)) (hm2 i)
  intro s hs
  have hs' := (mem_stdLat_iff _ s).1 hs
  choose p q hpq using fun i => (lattice_iff _ _).1 (hs' i)
  have hs_sum : s = ∑ i, Pi.single i (s i) := by
    exact (Finset.univ_sum_single s).symm
  rw [hs_sum, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have e : Pi.single i (s i) = ((p i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ +
      ((q i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ := by
    rw [hpq i]
    funext j
    by_cases h : j = i
    · subst h
      simp [Complex.real_smul]
    · simp [Pi.single_apply, h]
  rw [e, map_add, map_smul, map_smul, smul_add, nsmul_intCast_smul_comm, nsmul_intCast_smul_comm]
  exact add_mem (zsmul_mem (k1 i) _) (zsmul_mem (k2 i) _)

lemma comm_of_bounded (σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (h1 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N • σ s ∈ stdLat (cmL a b d ha hd lam hlam) m)
    (h2 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N' • σ.symm s ∈ stdLat (cmL a b d ha hd lam hlam) m) :
    relIdx (stdLat (cmL a b d ha hd lam hlam) m)
        (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m))
        (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 := by
  unfold PI.ULS.relIdx PI.ULS.imgLat
  refine ⟨?_, ?_⟩
  · rw [← AddSubgroup.relIndex_comap]
    refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    rw [AddSubgroup.mem_comap]
    show σ ((N : ℂ) • s) ∈ _
    rw [map_smul, natCast_smul_eq_nsmul]
    exact h1 s hs
  · refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN')
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine AddSubgroup.mem_map.mpr ⟨N' • σ.symm s, h2 s hs, ?_⟩
    show σ (N' • σ.symm s) = (N' : ℂ) • s
    rw [map_nsmul, LinearEquiv.apply_symm_apply, natCast_smul_eq_nsmul]

end PI.UnitaryGroupMassFormula.UnimodLocStd

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BetaSt

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Finset

theorem pairR_sum_right {f : ℕ} {ι : Type*} (s : Finset ι) (v : Fin f → ℝ) (g : ι → ℝ)
    (w : ι → Fin f → ℝ) : pairR v (∑ j ∈ s, g j • w j) = ∑ j ∈ s, g j * pairR v (w j) := by
  simp only [pairR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

theorem pairR_sum_left {f : ℕ} {ι : Type*} (s : Finset ι) (v : Fin f → ℝ) (g : ι → ℝ)
    (w : ι → Fin f → ℝ) : pairR (∑ j ∈ s, g j • w j) v = ∑ j ∈ s, g j * pairR (w j) v := by
  simp only [pairR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

theorem pairR_sub_left {f : ℕ} (u v w : Fin f → ℝ) : pairR (u - v) w = pairR u w - pairR v w := by
  simp only [pairR, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pairR_add_right {f : ℕ} (u v w : Fin f → ℝ) : pairR u (v + w) = pairR u v + pairR u w := by
  unfold pairR
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairR_smul_right {f : ℕ} (a : ℝ) (u v : Fin f → ℝ) : pairR u (a • v) = a * pairR u v := by
  simp only [pairR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem exists_int_avoid {f : ℕ} (Z : Finset (Fin f → ℝ)) (hZ : ∀ z ∈ Z, z ≠ 0) :
    ∃ t : Fin f → ℤ, ∀ z ∈ Z, ∑ j, z j * (t j : ℝ) ≠ 0 := by
  classical
  let P : (Fin f → ℝ) → Polynomial ℝ := fun z => ∑ j, Polynomial.C (z j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ z ∈ Z, P z ≠ 0 := by
    intro z hz h0
    apply hZ z hz
    funext j
    have h1 := congrArg (fun p => Polynomial.coeff p (j : ℕ)) h0
    simp only [P, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]) (by simp)] at h1
    simpa using h1
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℝ) ∉ Z.biUnion (fun z => (P z).roots.toFinset) := by
    by_contra h
    push_neg at h
    have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : ℝ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    exact hinf ((Z.biUnion (fun z => (P z).roots.toFinset)).finite_toSet.subset
      (by rintro _ ⟨n, rfl⟩; exact h n))
  refine ⟨fun j => (T : ℤ) ^ (j : ℕ), fun z hz h0 => ?_⟩
  apply hT
  rw [Finset.mem_biUnion]
  refine ⟨z, hz, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hP z hz), Polynomial.IsRoot]
  simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast at h0
  exact h0

theorem beta_holds : BetaStatement := by
  intro f b m hm SS χ₀ hχ₀ hχ₀nn
  classical
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · refine ⟨0, fun i => i.elim0, fun χ _ => ⟨0, by simp [pairR]⟩, fun χ _ _ _ => Subsingleton.elim _ _⟩
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩

  let B : Matrix (Fin f) (Fin f) ℝ := Matrix.of fun i k => b i k
  have hBunit : IsUnit B := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact b.linearIndependent
  let c : Fin f → (Fin f → ℝ) := fun j k => B⁻¹ k j
  have hpc : ∀ i j, pairR (b i) (c j) = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hBunit)) i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [pairR, B, c] using h

  have hSS : ∀ χ ∈ SS, ∃ z : Fin f → ℤ, χ = ∑ i, (z i : ℝ) • b i := by
    intro χ hχ
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hχ
    exact ⟨z, by rw [← hz]; simp [Int.cast_smul_eq_zsmul]⟩
  have hcoord : ∀ (z : Fin f → ℤ) j, pairR (∑ i, (z i : ℝ) • b i) (c j) = z j := by
    intro z j
    rw [pairR_sum_left]
    simp [hpc]

  have hint : ∀ χ ∈ SS, ∀ n : Fin f → ℤ, ∃ k : ℤ, pairR χ (∑ j, (n j : ℝ) • c j) = k := by
    intro χ hχ n
    obtain ⟨z, rfl⟩ := hSS χ hχ
    refine ⟨∑ j, n j * z j, ?_⟩
    rw [pairR_sum_right]
    simp [hcoord]

  have hcli : LinearIndependent ℝ c := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have := congrArg (fun v => pairR (b i) v) hg
    simp only [pairR_sum_right, hpc] at this
    simpa [pairR, Finset.sum_ite_eq, hi] using this
  let cb : Module.Basis (Fin f) ℝ (Fin f → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hcli (by simp)
  have hcb : ∀ j, cb j = c j := fun j => by simp [cb]
  set D : ℝ := ∑ j, ‖cb j‖ with hD
  let v : Fin f → ℝ := fun _ => D + 1
  let fl := ZSpan.floor cb v
  have hfl : ((fl : Fin f → ℝ)) = v - ZSpan.fract cb v := by rw [ZSpan.fract_apply]; abel
  have hfrac : ‖ZSpan.fract cb v‖ ≤ D := ZSpan.norm_fract_le cb v
  have hβ₀pos : ∀ k, 1 ≤ (fl : Fin f → ℝ) k := by
    intro k
    rw [hfl]
    have h1 : |ZSpan.fract cb v k| ≤ ‖ZSpan.fract cb v‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (ZSpan.fract cb v) k
    have h2 := le_abs_self (ZSpan.fract cb v k)
    have h3 : (v - ZSpan.fract cb v) k = D + 1 - ZSpan.fract cb v k := rfl
    rw [h3]
    linarith
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Fin f → ℤ, (fl : Fin f → ℝ) = ∑ j, (n₀ j : ℝ) • c j := by
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp fl.2
    exact ⟨z, by rw [← hz]; simp [Int.cast_smul_eq_zsmul, hcb]⟩
  obtain ⟨β₀, hβ₀fl⟩ : ∃ β₀ : Fin f → ℝ, β₀ = (fl : Fin f → ℝ) := ⟨_, rfl⟩
  rw [← hβ₀fl] at hβ₀pos hn₀
  set J : ℝ := pairR χ₀ β₀ with hJ
  have hpair_nonneg : ∀ χ : Fin f → ℝ, (∀ i, 0 ≤ χ i) → 0 ≤ pairR χ β₀ := by
    intro χ hχ
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hχ i) (le_trans zero_le_one (hβ₀pos i))
  have hcomp_le : ∀ χ : Fin f → ℝ, (∀ i, 0 ≤ χ i) → ∀ i, χ i ≤ pairR χ β₀ := by
    intro χ hχ i
    calc χ i ≤ χ i * β₀ i := le_mul_of_one_le_right (hχ i) (hβ₀pos i)
      _ ≤ pairR χ β₀ := Finset.single_le_sum (f := fun k => χ k * β₀ k)
          (fun k _ => mul_nonneg (hχ k) (le_trans zero_le_one (hβ₀pos k))) (Finset.mem_univ i)

  let sl : Set (Fin f → ℝ) := {χ | ∀ i, 0 ≤ χ i ∧ χ i ≤ J}
  have hslb : Bornology.IsBounded sl := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin f → ℝ)) (r := |J|)).subset ?_
    intro χ hχ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg J)).mpr fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ i).1]
    exact le_trans (hχ i).2 (le_abs_self J)
  have hfin : ((SS : Set (Fin f → ℝ)) ∩ sl).Finite := by
    simpa [Set.inter_comm] using ZSpan.setFinite_inter b hslb

  let w : (Fin f → ℝ) → (Fin f → ℝ) := fun χ j => pairR (χ - χ₀) (c j)
  let Z : Finset (Fin f → ℝ) := (hfin.toFinset.filter (fun χ => χ ≠ χ₀)).image w
  have hZ : ∀ z ∈ Z, z ≠ 0 := by
    intro z hz hz0
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hχ
    obtain ⟨⟨hχSS, -⟩, hne⟩ := hχ
    obtain ⟨z, hz'⟩ := hSS (χ - χ₀) (SS.sub_mem hχSS hχ₀)
    apply hne
    have : ∀ j, z j = 0 := by
      intro j
      have := congrFun hz0 j
      simp only [w, Pi.zero_apply] at this
      rw [hz', hcoord] at this
      exact_mod_cast this
    have : χ - χ₀ = 0 := by rw [hz']; simp [this]
    exact sub_eq_zero.mp this
  obtain ⟨t, ht⟩ := exists_int_avoid Z hZ
  set β' : Fin f → ℝ := ∑ j, (t j : ℝ) • c j with hβ'
  set M' : ℝ := ∑ i, |β' i| with hM'
  have hM'nn : 0 ≤ M' := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hβ'le : ∀ i, |β' i| ≤ M' := fun i =>
    Finset.single_le_sum (f := fun k => |β' k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have hbound : ∀ χ : Fin f → ℝ, (∀ i, 0 ≤ χ i) → |pairR χ β'| ≤ M' * pairR χ β₀ := by
    intro χ hχ
    calc |pairR χ β'| ≤ ∑ i, |χ i * β' i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, χ i * |β' i| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (hχ i)]
      _ ≤ ∑ i, χ i * (M' * β₀ i) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hχ i)
          calc |β' i| ≤ M' := hβ'le i
            _ ≤ M' * β₀ i := le_mul_of_one_le_right hM'nn (hβ₀pos i)
      _ = M' * pairR χ β₀ := by
          simp only [pairR, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
  have hJnn : 0 ≤ J := hpair_nonneg χ₀ hχ₀nn
  obtain ⟨R, hR⟩ : ∃ R : ℕ, M' * (2 * J + 1) < R := exists_nat_gt _
  set β'' : Fin f → ℝ := (R : ℝ) • β₀ + β' with hβ''
  refine ⟨(m : ℝ) • β'', fun i => ?_, fun χ hχ => ?_, fun χ hχ hχnn heq => ?_⟩
  ·
    have h1 := hβ₀pos i
    have h2 : -M' ≤ β' i := le_trans (neg_le_neg (hβ'le i)) (neg_abs_le _)
    have h3 : M' ≤ M' * (2 * J + 1) := le_mul_of_one_le_right hM'nn (by linarith)
    have h4 : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [Pi.smul_apply, smul_eq_mul, hβ'', Pi.add_apply]
    apply mul_pos h4
    nlinarith
  ·
    obtain ⟨k₁, hk₁⟩ := hint χ hχ n₀
    obtain ⟨k₂, hk₂⟩ := hint χ hχ t
    refine ⟨R * k₁ + k₂, ?_⟩
    have e1 : pairR χ β₀ = k₁ := by rw [hn₀]; exact hk₁
    have e2 : pairR χ β' = k₂ := by rw [hβ']; exact hk₂
    rw [pairR_smul_right, hβ'', pairR_add_right, pairR_smul_right, e1, e2]
    push_cast; ring
  ·
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [pairR_smul_right, pairR_smul_right] at heq
    have heq' := mul_left_cancel₀ hm0 heq
    rw [hβ'', pairR_add_right, pairR_add_right, pairR_smul_right, pairR_smul_right] at heq'
    obtain ⟨i₁, hi₁⟩ := hint χ hχ n₀
    obtain ⟨j₁, hj₁⟩ := hint χ₀ hχ₀ n₀
    rw [← hn₀] at hi₁ hj₁
    have hinn : (0 : ℝ) ≤ i₁ := hi₁ ▸ hpair_nonneg χ hχnn
    have hjnn : (0 : ℝ) ≤ j₁ := hj₁ ▸ hJnn
    by_cases hij : i₁ = j₁
    ·
      have hpe : pairR χ β' = pairR χ₀ β' := by
        have : pairR χ β₀ = pairR χ₀ β₀ := by rw [hi₁, hj₁, hij]
        rw [this] at heq'
        linarith
      by_contra hne
      have hmem : χ ∈ hfin.toFinset.filter (fun χ => χ ≠ χ₀) := by
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        refine ⟨⟨hχ, fun i => ⟨hχnn i, ?_⟩⟩, hne⟩
        have := hcomp_le χ hχnn i
        rw [hi₁, hij, ← hj₁] at this
        exact this
      have hwz := ht (w χ) (Finset.mem_image_of_mem w hmem)
      apply hwz
      have : ∑ j, w χ j * (t j : ℝ) = pairR (χ - χ₀) β' := by
        rw [hβ', pairR_sum_right]
        refine Finset.sum_congr rfl fun j _ => by simp [w]; ring
      rw [this, pairR_sub_left, hpe, sub_self]
    · exfalso
      have hdiff : (R : ℝ) * ((i₁ : ℝ) - j₁) = pairR χ₀ β' - pairR χ β' := by
        rw [← hi₁, ← hj₁]; linarith
      have hb1 := hbound χ hχnn
      have hb2 := hbound χ₀ hχ₀nn
      rw [hi₁] at hb1
      rw [hj₁] at hb2
      have hJ' : J = j₁ := by rw [hJ, hj₁]
      have habs : |(R : ℝ) * ((i₁ : ℝ) - j₁)| ≤ M' * (i₁ + j₁) := by
        rw [hdiff]
        calc |pairR χ₀ β' - pairR χ β'| ≤ |pairR χ₀ β'| + |pairR χ β'| := abs_sub _ _
          _ ≤ M' * j₁ + M' * i₁ := add_le_add hb2 hb1
          _ = M' * (i₁ + j₁) := by ring
      have hne : (1 : ℝ) ≤ |(i₁ : ℝ) - j₁| := by
        have : (i₁ - j₁ : ℤ) ≠ 0 := sub_ne_zero.mpr hij
        have h := Int.one_le_abs this
        exact_mod_cast h
      have hkey : (i₁ : ℝ) + j₁ ≤ (2 * j₁ + 1) * |(i₁ : ℝ) - j₁| := by
        rcases lt_or_gt_of_ne hij with h | h
        · have h1 : (i₁ : ℝ) + 1 ≤ j₁ := by exact_mod_cast h
          rw [abs_of_nonpos (by linarith)]
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ j₁ - i₁ by linarith)
            (show (0 : ℝ) ≤ 2 * j₁ + 1 by linarith)]
        · have h1 : (j₁ : ℝ) + 1 ≤ i₁ := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ i₁ - j₁ by linarith)
            (show (0 : ℝ) ≤ 2 * j₁ by linarith)]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg R)] at habs
      rw [hJ'] at hR
      have : (R : ℝ) * |(i₁ : ℝ) - j₁| ≤ M' * ((2 * j₁ + 1) * |(i₁ : ℝ) - j₁|) :=
        le_trans habs (mul_le_mul_of_nonneg_left hkey hM'nn)
      nlinarith [abs_nonneg ((i₁ : ℝ) - j₁)]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

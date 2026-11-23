import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal

noncomputable section

variable {p q : ℕ}

theorem sumBd_id (A0 B s : ℝ) (N j : ℕ) (hB : 0 ≤ B) :
    (A0 * ((2 : ℝ) ^ j) ^ 2) ^ N * (B / 4 ^ j) ^ s = A0 ^ N * B ^ s * ((4 : ℝ) ^ N / 4 ^ s) ^ j := by
  have h4 : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h5 : ((4 : ℝ) ^ j) ^ s = ((4 : ℝ) ^ s) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [h4, Real.div_rpow hB (by positivity), mul_pow, div_pow, h5]
  have h6 : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
  field_simp
  ring

theorem sumBd_w_le_one {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (Complex.normSq (det M.toBlocks₂₂))⁻¹ ^ s ∧ (Complex.normSq (det M.toBlocks₂₂))⁻¹ ^ s ≤ 1 := by
  have h1 := sumBd_detD_ge h
  have h2 := sumBdFsq_nonneg M.toBlocks₁₂
  have hN : 1 ≤ Complex.normSq (det M.toBlocks₂₂) := by linarith
  have hpos : 0 < Complex.normSq (det M.toBlocks₂₂) := by linarith
  have hinv : (Complex.normSq (det M.toBlocks₂₂))⁻¹ ≤ 1 := by
    first
      | exact inv_le_one_of_one_le₀ hN
      | exact inv_le_one hN
  exact ⟨Real.rpow_nonneg (inv_nonneg.2 hpos.le) _, Real.rpow_le_one (inv_nonneg.2 hpos.le) hinv hs⟩

theorem sumBd_w_le_big {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) {s R : ℝ} (hs : 0 ≤ s)
    (hR : 0 < R) {i j : Fin p ⊕ Fin q} (hij : R < ‖M i j‖) :
    (Complex.normSq (det M.toBlocks₂₂))⁻¹ ^ s ≤ ((((p + q : ℕ) : ℝ) + 1) / R ^ 2) ^ s := by
  have h1 := sumBd_detD_ge h
  have h2 := sumBdFsq_nonneg M.toBlocks₁₂
  have hpos : 0 < Complex.normSq (det M.toBlocks₂₂) := by linarith
  have he := sumBd_entry_bound h i j
  have hR2 : R ^ 2 < Complex.normSq (M i j) := by
    have := Complex.normSq_eq_norm_sq (M i j)
    nlinarith [norm_nonneg (M i j)]
  have hc : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hle : (Complex.normSq (det M.toBlocks₂₂))⁻¹ ≤ (((p + q : ℕ) : ℝ) + 1) / R ^ 2 := by
    rw [inv_le_comm₀ hpos (by positivity), inv_div, div_le_iff₀ hc]
    linarith [mul_comm (Complex.normSq (det M.toBlocks₂₂)) (((p + q : ℕ) : ℝ) + 1)]
  exact Real.rpow_le_rpow (inv_nonneg.2 hpos.le) hle hs

theorem sumBd_prod_le_big {f : ℕ} (w : Fin f → ℝ) (h0 : ∀ k, 0 ≤ w k) (h1 : ∀ k, w k ≤ 1) (k0 : Fin f)
    {b : ℝ} (hb : w k0 ≤ b) : ∏ k, w k ≤ b := by
  rw [← Finset.mul_prod_erase Finset.univ w (Finset.mem_univ k0)]
  have h2 : ∏ k ∈ Finset.univ.erase k0, w k ≤ 1 := Finset.prod_le_one (fun k _ => h0 k) (fun k _ => h1 k)
  have h3 : 0 ≤ ∏ k ∈ Finset.univ.erase k0, w k := Finset.prod_nonneg fun k _ => h0 k
  nlinarith [h0 k0]

theorem sumBd_count_real {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (hU : ∀ a k, IsUpq (x a k)) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ a b, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖)
    {R : ℝ} (hR : 1 ≤ R) :
    (({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (((4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2) ^ (f * ((p + q) * ((p + q) * 2)))) := by
  have hpq : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hR0 : (0 : ℝ) < R := by linarith
  set η : ℝ := c / (((p + q : ℕ) : ℝ) + 1) / R / 2 with hη_def
  have hη : 0 < η := by positivity
  have hsep2 : ∀ a, (∀ k i j, ‖x a k i j‖ ≤ R) → ∀ b, (∀ k i j, ‖x b k i j‖ ≤ R) → a ≠ b →
      ∃ k i j, 2 * η ≤ ‖x b k i j - x a k i j‖ := by
    intro a ha b _ hab
    obtain ⟨k, i, j, hk⟩ := hsep a b hab
    obtain ⟨l, hl⟩ := sumBd_sep_diff (hU a k) hR0 hc (ha k) hk
    refine ⟨k, i, l, ?_⟩
    have h2η : 2 * η = c / (((p + q : ℕ) : ℝ) + 1) / R := by rw [hη_def]; ring
    rw [h2η]
    exact hl
  have hE : Fintype.card (Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool) = f * ((p + q) * ((p + q) * 2)) := by
    simp [Fintype.card_prod, Fintype.card_sum]
  have hcount := sumBd_count x hη hsep2
  rw [Fintype.card_piFinset, Finset.prod_const, Int.card_Icc, Finset.card_univ, hE] at hcount
  have hm0 : (0 : ℤ) ≤ ⌈R / η⌉ := Int.ceil_nonneg (by positivity)
  have hbase : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) ≤ (4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2 := by
    have h1 : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) = 2 * (⌈R / η⌉ : ℝ) + 1 := by
      have h0 : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℤ) = ⌈R / η⌉ + 1 - -⌈R / η⌉ :=
        Int.toNat_of_nonneg (by omega)
      have h0' : (((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) = ((⌈R / η⌉ + 1 - -⌈R / η⌉ : ℤ) : ℝ) := by
        exact_mod_cast h0
      rw [h0']
      push_cast
      ring
    have h2 : (⌈R / η⌉ : ℝ) < R / η + 1 := Int.ceil_lt_add_one _
    have h3 : R / η = 2 * (((p + q : ℕ) : ℝ) + 1) * R ^ 2 / c := by
      rw [hη_def]
      field_simp
    have hR2 : 1 ≤ R ^ 2 := by nlinarith
    have h5 : (4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2 = 2 * (R / η) + 3 * R ^ 2 := by
      rw [h3]
      ring
    rw [h1, h5]
    linarith
  calc ((({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard : ℝ≥0∞))
      ≤ ((((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat ^ (f * ((p + q) * ((p + q) * 2))) : ℕ) : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 hcount
    _ = ENNReal.ofReal ((((⌈R / η⌉ + 1 - -⌈R / η⌉).toNat : ℕ) : ℝ) ^ (f * ((p + q) * ((p + q) * 2)))) := by
        rw [ENat.toENNReal_coe, ← Nat.cast_pow, ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _)

theorem sumBd_sum {f : ℕ} {s c : ℝ} (hs : 2 * (f : ℝ) * ((p + q : ℕ) : ℝ) ^ 2 < s) (hc : 0 < c) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a k, IsUpq (x a k)) →
      (∀ a b, a ≠ b → ∃ k i j,
        c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) →
      ∑' a, ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s) ≤ C := by
  classical
  set P : ℝ := ((p + q : ℕ) : ℝ) with hP
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  set K : ℝ := 4 * (P + 1) / c + 3 with hK
  have hK0 : 0 ≤ K := by positivity
  set D : ℕ := f * ((p + q) * ((p + q) * 2)) with hD
  set B : ℝ := 4 * (P + 1) with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hDs : (D : ℝ) < s := by
    have : (D : ℝ) = 2 * (f : ℝ) * P ^ 2 := by rw [hD, hP]; push_cast; ring
    rw [this]; exact hs
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg _) hDs.le
  set ρ : ℝ := (4 : ℝ) ^ D / 4 ^ s with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity), ← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hDs
  refine ⟨ENNReal.ofReal (K ^ D * B ^ s) * ∑' j : ℕ, ENNReal.ofReal (ρ ^ j), ?_, ?_⟩
  · have hg : ∑' j : ℕ, ENNReal.ofReal (ρ ^ j) = (1 - ENNReal.ofReal ρ)⁻¹ := by
      rw [← ENNReal.tsum_geometric]
      exact tsum_congr fun j => ENNReal.ofReal_pow hρ0 j
    rw [hg]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    rw [ENNReal.inv_lt_top]
    exact tsub_pos_of_lt (ENNReal.ofReal_lt_one.mpr hρ1)
  intro ι x hU hsep
  set Bs : ℕ → Set ι := fun m => {a | ∀ k i j, ‖x a k i j‖ ≤ (2 : ℝ) ^ m} with hBs
  set g : ι → ℝ≥0∞ := fun a => ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s)
    with hgdef
  have hex : ∀ a, ∃ m, a ∈ Bs m := by
    intro a
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (∑ k, ∑ i, ∑ j, ‖x a k i j‖) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, fun k i j => le_trans ?_ hm.le⟩
    calc ‖x a k i j‖ ≤ ∑ j', ‖x a k i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖x a k i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖x a k i' j'‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖x a k i' j'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ k', ∑ i', ∑ j', ‖x a k' i' j'‖ :=
          Finset.single_le_sum (f := fun k' => ∑ i', ∑ j', ‖x a k' i' j'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ k)
  have hw0 : ∀ a k, 0 ≤ (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s := fun a k =>
    (sumBd_w_le_one (hU a k) hs0).1
  have hw1 : ∀ a k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s ≤ 1 := fun a k =>
    (sumBd_w_le_one (hU a k) hs0).2
  have hpt : ∀ a, g a ≤ ∑' m : ℕ, (Bs m).indicator (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)) a := by
    intro a
    let m0 := Nat.find (hex a)
    have hm0 : a ∈ Bs m0 := Nat.find_spec (hex a)
    refine le_trans ?_ (ENNReal.le_tsum m0)
    rw [Set.indicator_of_mem hm0]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases Nat.eq_zero_or_pos m0 with h0 | hpos
    · rw [h0, pow_zero, div_one]
      calc ∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s ≤ 1 :=
            Finset.prod_le_one (fun k _ => hw0 a k) (fun k _ => hw1 a k)
        _ ≤ B ^ s := Real.one_le_rpow hB1 hs0
    · obtain ⟨m, hm⟩ : ∃ m, m0 = m + 1 := ⟨m0 - 1, by omega⟩
      have hnot : a ∉ Bs m := Nat.find_min (hex a) (by omega)
      simp only [hBs, Set.mem_setOf_eq, not_forall, not_le] at hnot
      obtain ⟨k, i, j, hkij⟩ := hnot
      have hbig := sumBd_w_le_big (hU a k) hs0 (by positivity : (0 : ℝ) < 2 ^ m) hkij
      have hfac : (P + 1) / ((2 : ℝ) ^ m) ^ 2 = B / 4 ^ m0 := by
        have h4 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [h4, hm, hB, pow_succ]
        field_simp
      rw [hfac] at hbig
      exact sumBd_prod_le_big _ (hw0 a) (hw1 a) k hbig
  calc ∑' a, ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s)
      = ∑' a, g a := rfl
    _ ≤ ∑' a, ∑' m : ℕ, (Bs m).indicator (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)) a :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' m : ℕ, ∑' a, (Bs m).indicator (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)) a :=
        ENNReal.tsum_comm
    _ = ∑' m : ℕ, (Bs m).encard * ENNReal.ofReal ((B / 4 ^ m) ^ s) := by
        refine tsum_congr fun m => ?_
        rw [← tsum_subtype (Bs m) (fun _ => ENNReal.ofReal ((B / 4 ^ m) ^ s)), ENNReal.tsum_set_const]
    _ ≤ ∑' m : ℕ, ENNReal.ofReal ((K * ((2 : ℝ) ^ m) ^ 2) ^ D) * ENNReal.ofReal ((B / 4 ^ m) ^ s) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        gcongr
        exact sumBd_count_real x hU hc hsep (R := (2 : ℝ) ^ m) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    _ = ∑' m : ℕ, ENNReal.ofReal (K ^ D * B ^ s) * ENNReal.ofReal (ρ ^ m) := by
        refine tsum_congr fun m => ?_
        rw [← ENNReal.ofReal_mul (by positivity), sumBd_id K B s D m (by linarith),
          ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (K ^ D * B ^ s) * ∑' j : ℕ, ENNReal.ofReal (ρ ^ j) := ENNReal.tsum_mul_left

end

end ReciprocityTheory.ChartRestriction.G.AR.Up

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulusStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.ZeroSum

theorem mem_disc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosBox χ (1 / 2) T) :
    ⌊ρ.im⌋ ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ ∧ ρ ∈ zerosDisc χ (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I) 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [abs_le] at h3
  have a1 := Int.floor_le ρ.im
  have a2 := Int.lt_floor_add_one ρ.im
  have a3 := Int.le_ceil T
  refine ⟨?_, ?_, Or.inr ?_, h4⟩
  · rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (⌈T⌉ : ℤ) := by linarith
      exact_mod_cast this
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have b1 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).re| ≤ 2 := by
      rw [abs_le]; simp; constructor <;> linarith
    have b2 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im| ≤ 1 := by
      have : (ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im = ρ.im - ⌊ρ.im⌋ := by simp
      rw [this, abs_le]; constructor <;> linarith
    linarith
  · rintro rfl
    simp at h2

theorem total_count : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
    2 ≤ T → ∃ h : (zerosBox χ (1 / 2) T).Finite,
      ∑ ρ ∈ h.toFinset, (ord χ ρ : ℝ) ≤ C * (q * T ^ 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
  refine ⟨12 * C, by positivity, fun q _ χ T hT => ?_⟩
  have hf : ∀ n : ℤ, (zerosDisc χ (2 + ((n : ℝ) : ℂ) * I) 3).Finite :=
    fun n => (H q χ 2 n 0 (by norm_num) le_rfl).1
  have hfin : (zerosBox χ (1 / 2) T).Finite := by
    refine ((Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet.biUnion (fun n _ => hf n)).subset ?_
    intro ρ hρ
    simp only [Set.mem_iUnion]
    exact ⟨_, (mem_disc χ hρ).1, (mem_disc χ hρ).2⟩
  refine ⟨hfin, ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have a3 := Int.ceil_lt_add_one T
  have a4 := Int.le_ceil T
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc (-⌈T⌉) ⌈T⌉) (g := fun ρ : ℂ => ⌊ρ.im⌋)
    (fun ρ hρ => (mem_disc χ (hfin.mem_toFinset.1 hρ)).1)]
  have key : ∀ n ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
      ∑ ρ ∈ hfin.toFinset with ⌊ρ.im⌋ = n, (ord χ ρ : ℝ) ≤ C * (q * (3 * T)) := by
    intro n hn
    have h2 := (H q χ 2 n 0 (by norm_num) le_rfl).2.1
    rw [finsum_mem_eq_finite_toFinset_sum _ (hf n)] at h2
    have hn' : |(n : ℝ)| ≤ T + 1 := by
      rw [Finset.mem_Icc] at hn
      have c1 : ((-⌈T⌉ : ℤ) : ℝ) ≤ n := by exact_mod_cast hn.1
      have c2 : (n : ℝ) ≤ (⌈T⌉ : ℤ) := by exact_mod_cast hn.2
      push_cast at c1
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ ∑ ρ ∈ (hf n).toFinset, (ord χ ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
          intro ρ hρ
          rw [Finset.mem_filter] at hρ
          rw [Set.Finite.mem_toFinset, ← hρ.2]
          exact (mem_disc χ (hfin.mem_toFinset.1 hρ.1)).2
      _ ≤ _ := h2
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          refine (Real.log_le_self (by positivity)).trans ?_
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℝ) ≤ 4 * T := by
    have h0 : (0 : ℤ) ≤ ⌈T⌉ + 1 - -⌈T⌉ := by
      have : (0 : ℤ) ≤ ⌈T⌉ := Int.ceil_nonneg (by linarith)
      omega
    have : (((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℤ) : ℝ) = ((⌈T⌉ + 1 - -⌈T⌉ : ℤ) : ℝ) := by
      rw [Int.card_Icc, Int.toNat_of_nonneg h0]
    push_cast at this
    rw [this]; linarith
  calc _ ≤ (4 * T) * (C * (q * (3 * T))) := by gcongr
    _ = _ := by ring

theorem layers {ι : Type*} (s : Finset ι) (w δ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {L η e : ℝ}
    (hL : 0 < L) (J : ℕ) (hJ : L * e < J) (hη : 0 ≤ η) :
    ∑ i ∈ s with η ≤ δ i, w i * Real.exp (-(L * δ i)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ i ∈ s with δ i ≤ min (η + (j + 1) / L) e, w i) + Real.exp (-(L * e)) * ∑ i ∈ s, w i := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hwi := hw i
  have hnn : ∀ j ∈ Finset.range J, 0 ≤ Real.exp (-(L * η) - j) *
      (if δ i ≤ min (η + (j + 1) / L) e then w i else 0) := by
    intro j _
    split_ifs <;> positivity
  have hs := Finset.sum_nonneg hnn
  have he : 0 ≤ Real.exp (-(L * e)) * w i := by positivity
  split_ifs with h
  · by_cases h2 : δ i ≤ e
    · have h0 : 0 ≤ L * (δ i - η) := mul_nonneg hL.le (by linarith)
      have a1 := Nat.floor_le h0
      have a2 := Nat.lt_floor_add_one (L * (δ i - η))
      have hm : ⌊L * (δ i - η)⌋₊ ∈ Finset.range J := by
        rw [Finset.mem_range, Nat.floor_lt h0]
        nlinarith
      have := Finset.single_le_sum hnn hm
      rw [if_pos] at this
      · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * η) - ⌊L * (δ i - η)⌋₊) :=
          Real.exp_le_exp.2 (by linarith)
        nlinarith
      · refine le_min ?_ h2
        have : δ i - η ≤ (⌊L * (δ i - η)⌋₊ + 1) / L := by
          rw [le_div_iff₀ hL]; linarith
        linarith
    · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * e)) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith
  · linarith

theorem sum_rpow_zeros_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  obtain ⟨A₁, C₁, η₁, hA₁, hC₁, hη₁, H₁⟩ := GlobalTheory.T.logFree_zeroDensity_dirichlet_one_modulus
  obtain ⟨C₂, hC₂, H₂⟩ := total_count
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ η₁ ∧ e ≤ 1 / 2 :=
    ⟨min η₁ (1 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  have hr : Real.exp (-1 / 2) < 1 := by
    simpa using Real.exp_lt_exp.2 (show (-1 / 2 : ℝ) < 0 by norm_num)
  have hsum := summable_geometric_of_lt_one (Real.exp_pos (-1 / 2)).le hr
  set K := ∑' j : ℕ, Real.exp (-1 / 2) ^ j with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => by positivity
  refine ⟨2 * A₁ + 4 / e, C₁ * Real.exp (1 / 2) * K + C₂, e / 2, by positivity, by positivity,
    by positivity, fun q _ T u η hT hu hη => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqT : (1 : ℝ) < q * T := by nlinarith
  have hu1 : 1 < u := (Real.one_lt_rpow hqT (by positivity)).trans_le hu
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log u := Real.log_pos hu1
  have hM : 0 < Real.log (q * T) := Real.log_pos hqT
  have hLM : (2 * A₁ + 4 / e) * Real.log (q * T) ≤ Real.log u := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by positivity) hu
  set L := Real.log u with hLdef
  set M := Real.log (q * T) with hMdef
  have h4 : 0 < 4 / e := by positivity
  have hLM1 : 2 * A₁ * M ≤ L := by nlinarith
  have hLM2 : 4 * M ≤ e * L := by
    have : 4 / e * M ≤ L := by nlinarith [mul_pos hA₁ hM]
    rw [div_mul_eq_mul_div, div_le_iff₀ he0] at this
    linarith
  choose hfin hcount using fun χ : DirichletCharacter ℂ q => H₂ q χ T hT
  obtain ⟨J, hJ⟩ := exists_nat_gt (L * e)
  have step1 : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) +
        Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) := by
    intro χ
    have h := layers (hfin χ).toFinset (fun ρ => (ord χ ρ : ℝ)) (fun ρ => 1 - ρ.re)
      (fun _ => Nat.cast_nonneg _) hL J hJ hη
    have e1 : zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η} =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => η ≤ 1 - ρ.re) : Finset ℂ) := by
      ext ρ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
      exact and_congr_right fun _ => ⟨fun _ => by linarith, fun _ => by linarith⟩
    have e2 : ∀ x : ℝ, x ≤ e → zerosBox χ (1 - x) T =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => 1 - ρ.re ≤ x) : Finset ℂ) := by
      intro x hx
      ext ρ
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, zerosBox]
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨by linarith, b, c, d⟩, by linarith⟩
      · rintro ⟨⟨a, b, c, d⟩, f⟩
        exact ⟨by linarith, b, c, d⟩
    rw [e1, finsum_mem_coe_finset]
    calc _ = _ := by
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Real.rpow_def_of_pos hu0, show Real.log u * (ρ.re - 1) = -(L * (1 - ρ.re)) by ring]
      _ ≤ _ := h
      _ ≤ _ := by
          refine add_le_add (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
            (mul_le_mul_of_nonneg_left (hcount χ) (Real.exp_pos _).le)
          rw [e2 _ (min_le_right _ _), finsum_mem_coe_finset]
  refine (Finset.sum_le_sum fun χ _ => step1 χ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hA : ∑ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * K * u ^ (-η / 2) := by
    have : ∀ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * Real.exp (-1 / 2) ^ j := by
      intro j _
      rw [← Finset.mul_sum]
      have hx0 : 0 ≤ min (η + (j + 1) / L) e := by positivity
      have hx1 := min_le_left (η + (j + 1) / L) e
      have hx2 := min_le_right (η + (j + 1) / L) e
      generalize min (η + (j + 1) / L) e = x at hx0 hx1 hx2 ⊢
      have h := H₁ q T (1 - x) hT (by linarith) (by linarith)
      refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans ?_
      rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (by linarith), ← Real.exp_nat_mul,
        mul_left_comm, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
      rw [← hLdef, ← hMdef]
      have hx3 : L * x ≤ L * η + (j + 1) := by
        have := mul_le_mul_of_nonneg_left hx1 hL.le
        rwa [mul_add, mul_div_cancel₀ _ hL.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_right hLM1 hx0]
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    have := hsum.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)
    calc _ ≤ C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * K := by gcongr
      _ = _ := by ring
  have hB : ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) ≤
      C₂ * u ^ (-(e / 2)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have ht : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hE : Real.exp (2 * M) = (q * T) ^ 2 := by
      rw [show 2 * M = M + M by ring, Real.exp_add, hMdef, Real.exp_log (by linarith), sq]
    calc _ ≤ (q : ℝ) * (Real.exp (-(L * e)) * (C₂ * (q * T ^ 2))) := by gcongr
      _ = C₂ * (Real.exp (-(L * e)) * Real.exp (2 * M)) := by rw [hE]; ring
      _ ≤ _ := by
        rw [← Real.exp_add, Real.rpow_def_of_pos hu0, ← hLdef]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
        linarith
  have p1 : 0 ≤ u ^ (-η / 2) := by positivity
  have p2 : 0 ≤ u ^ (-(e / 2)) := by positivity
  have p3 : 0 ≤ C₁ * Real.exp (1 / 2) * K := by positivity
  nlinarith [mul_nonneg p3 p2, mul_nonneg hC₂.le p1]

end GlobalTheory.Lin.ZeroSum

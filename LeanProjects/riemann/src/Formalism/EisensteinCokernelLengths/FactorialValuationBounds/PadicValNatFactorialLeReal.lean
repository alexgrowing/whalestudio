import Formalism.EisensteinCokernelLengths.ExponentChainBound
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
import Formalism.WindowSums.PowerSeriesRelationList

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

open Polynomial

lemma sum_range_padicValNat_succ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ∑ k ∈ Finset.range n, padicValNat ℓ (k + 1) = padicValNat ℓ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n), add_comm]

lemma padicValNat_factorial_le_real (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (n : ℕ) :
    (padicValNat ℓ n.factorial : ℝ) ≤ (n : ℝ) / ((ℓ : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.out.two_le
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hpos]
  have h := sub_one_mul_padicValNat_factorial (p := ℓ) n
  have h' : (ℓ - 1) * padicValNat ℓ n.factorial ≤ n := by rw [h]; exact Nat.sub_le _ _
  have h'' : (((ℓ - 1) * padicValNat ℓ n.factorial : ℕ) : ℝ) ≤ n := by exact_mod_cast h'
  rw [Nat.cast_mul, Nat.cast_sub hℓ.out.one_le, Nat.cast_one] at h''
  linarith

lemma sum_padicValInt_le_factorial (ℓ : ℕ) [Fact ℓ.Prime] (A : Finset ℤ) (n : ℕ)
    (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ n) :
    ∑ t ∈ A, padicValInt ℓ t ≤ padicValNat ℓ n.factorial := by
  rw [← sum_range_padicValNat_succ]
  have hinj : Set.InjOn (fun t : ℤ => t.toNat - 1) A := by
    intro x hx y hy hxy
    have := hA x hx; have := hA y hy
    simp only at hxy
    omega
  calc ∑ t ∈ A, padicValInt ℓ t
      = ∑ k ∈ A.image (fun t : ℤ => t.toNat - 1), padicValNat ℓ (k + 1) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun t ht => ?_
        have := hA t ht
        unfold padicValInt
        congr 1
        omega
    _ ≤ ∑ k ∈ Finset.range n, padicValNat ℓ (k + 1) := by
        apply Finset.sum_le_sum_of_subset
        intro k hk
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
        have := hA t ht
        rw [Finset.mem_range]
        omega

lemma sum_comp_le_factorial (ℓ : ℕ) [Fact ℓ.Prime] (A : Finset ℤ) (f : ℤ → ℤ)
    (hf : Set.InjOn f A) (n : ℕ) (hA : ∀ j ∈ A, 1 ≤ f j ∧ f j ≤ n) :
    ((∑ j ∈ A, padicValInt ℓ (f j) : ℕ) : ℝ) ≤ (n : ℝ) / ((ℓ : ℝ) - 1) := by
  have h := Finset.sum_image (f := padicValInt ℓ) hf
  rw [← h]
  refine le_trans (Nat.cast_le.mpr (sum_padicValInt_le_factorial ℓ _ n ?_))
    (padicValNat_factorial_le_real ℓ n)
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  exact hA j hj

lemma sum_comp_le_window (ℓ : ℕ) [Fact ℓ.Prime] (A : Finset ℤ) (f : ℤ → ℤ) (hf : Set.InjOn f A)
    (lo : ℤ) (L D : ℕ) (hA : ∀ j ∈ A, lo ≤ f j ∧ f j < lo + L ∧ f j ≠ 0 ∧ |f j| ≤ D) :
    ((∑ j ∈ A, padicValInt ℓ (f j) : ℕ) : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  have h := Finset.sum_image (f := padicValInt ℓ) hf
  rw [← h]
  apply Formalism.WindowSums.arc_WindowSum ℓ lo L D
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, h2, -, -⟩ := hA j hj
    exact Finset.mem_Ico.mpr ⟨h1, h2⟩
  · intro ht
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp ht
    exact (hA j hj).2.2.1 hj0
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact (hA j hj).2.2.2

lemma gap_bound (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (a S η b : ℕ) (R₁ R₂ : Finset ℤ)
    (hab : 2 * a + η ≤ b)
    (h1 : R₁ ⊆ Finset.Icc ((b : ℤ) - a + 1) b)
    (h2 : R₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (j₀ : ℤ) (hj₀ : j₀ ∈ R₁) :
    (((∑ j ∈ R₂, padicValInt ℓ (j₀ - j)) + ∑ j ∈ R₁.erase j₀, padicValInt ℓ (j₀ - j) : ℕ) : ℝ) ≤
      ((3 * a + S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ ((b + η : ℕ) : ℝ) := by
  have hj := Finset.mem_Icc.mp (h1 hj₀)
  have h2' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.out.two_le
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hdisj : Disjoint R₂ (R₁.erase j₀) := by
    rw [Finset.disjoint_left]
    intro j hj2 hj1
    have := Finset.mem_Icc.mp (h1 (Finset.mem_of_mem_erase hj1))
    rcases Finset.mem_union.mp (h2 hj2) with h | h <;> have := Finset.mem_Icc.mp h <;> omega
  rw [← Finset.sum_union hdisj]
  have hmem : ∀ j ∈ R₂ ∪ R₁.erase j₀, j ≠ j₀ ∧
      ((1 - (η : ℤ) ≤ j ∧ j ≤ η + a) ∨ ((b : ℤ) - a + 1 ≤ j ∧ j ≤ b + S + a)) := by
    intro j hjA
    rcases Finset.mem_union.mp hjA with h | h
    · rcases Finset.mem_union.mp (h2 h) with h' | h' <;> have := Finset.mem_Icc.mp h' <;> omega
    · have hne := Finset.ne_of_mem_erase h
      have := Finset.mem_Icc.mp (h1 (Finset.mem_of_mem_erase h))
      omega
  set A := R₂ ∪ R₁.erase j₀ with hAdef
  rw [← Finset.sum_filter_add_sum_filter_not A (fun j => j ≤ (η : ℤ) + a),
    ← Finset.sum_filter_add_sum_filter_not (A.filter fun j => ¬ j ≤ (η : ℤ) + a)
      (fun j => j < j₀), Nat.cast_add, Nat.cast_add]
  have hfar := sum_comp_le_window ℓ (A.filter fun j => j ≤ (η : ℤ) + a) (fun j => j₀ - j)
    (by intro x _ y _ h; simp only at h; omega) (j₀ - η - a) (a + 2 * η) (b + η) (by
      intro j hjf
      obtain ⟨hjA, hjle⟩ := Finset.mem_filter.mp hjf
      have := hmem j hjA
      refine ⟨by omega, by push_cast; omega, by omega, ?_⟩
      rw [abs_le]; push_cast; constructor <;> omega)
  have hlo := sum_comp_le_factorial ℓ
    ((A.filter fun j => ¬ j ≤ (η : ℤ) + a).filter fun j => j < j₀) (fun j => j₀ - j)
    (by intro x _ y _ h; simp only at h; omega) (j₀ - ((b : ℤ) - a + 1)).toNat (by
      intro j hjf
      simp only [Finset.mem_filter] at hjf
      obtain ⟨⟨hjA, hjle⟩, hjlt⟩ := hjf
      have := hmem j hjA
      omega)
  have hsymm : ∑ j ∈ (A.filter fun j => ¬ j ≤ (η : ℤ) + a).filter (fun j => ¬ j < j₀),
      padicValInt ℓ (j₀ - j) =
      ∑ j ∈ (A.filter fun j => ¬ j ≤ (η : ℤ) + a).filter (fun j => ¬ j < j₀),
      padicValInt ℓ (j - j₀) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold padicValInt
    rw [← Int.natAbs_neg, neg_sub]
  have hhi := sum_comp_le_factorial ℓ
    ((A.filter fun j => ¬ j ≤ (η : ℤ) + a).filter fun j => ¬ j < j₀) (fun j => j - j₀)
    (by intro x _ y _ h; simp only at h; omega) ((b : ℤ) + S + a - j₀).toNat (by
      intro j hjf
      simp only [Finset.mem_filter] at hjf
      obtain ⟨⟨hjA, hjle⟩, hjlt⟩ := hjf
      have := hmem j hjA
      omega)
  rw [hsymm]
  have hnat : (a + 2 * η) + (j₀ - ((b : ℤ) - a + 1)).toNat + ((b : ℤ) + S + a - j₀).toNat ≤
      3 * a + S + 2 * η := by omega
  have key : ((a + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) +
      (((j₀ - ((b : ℤ) - a + 1)).toNat : ℕ) : ℝ) / ((ℓ : ℝ) - 1) +
      ((((b : ℤ) + S + a - j₀).toNat : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤
      ((3 * a + S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hpos.le
    exact_mod_cast hnat
  linarith

lemma kill_of_mem_span {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    (T : Module.End R V) (P₁ P₂ : R[X]) (r : R) (x : V)
    (h : C r ∈ Ideal.span ({P₁, P₂} : Set R[X])) (h1 : aeval T P₁ x = 0)
    (h2 : aeval T P₂ x = 0) : r • x = 0 := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h
  have h3 : aeval T (C r) x = 0 := by
    rw [← hab, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, h1, h2, map_zero, map_zero, add_zero]
  rwa [aeval_C, Module.algebraMap_end_apply] at h3

lemma assoc_pow_valuation {ℓ : ℕ} [Fact ℓ.Prime] {y : ℤ_[ℓ]} (hy : y ≠ 0) :
    Associated y ((ℓ : ℤ_[ℓ]) ^ y.valuation) := by
  have h := PadicInt.unitCoeff_spec hy
  refine ⟨(PadicInt.unitCoeff hy)⁻¹, ?_⟩
  calc y * ↑(PadicInt.unitCoeff hy)⁻¹ =
      (↑(PadicInt.unitCoeff hy) * (ℓ : ℤ_[ℓ]) ^ y.valuation) * ↑(PadicInt.unitCoeff hy)⁻¹ := by rw [← h]
    _ = _ := by rw [mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem gapG_proof : GapG := by
  intro ℓ _ V _ _ T c hc a S η b E R₁ R₂ x hab h1 h2 hx1 hx2 hE
  have hdisj : Disjoint R₁ R₂ := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have := Finset.mem_Icc.mp (h1 hj1)
    rcases Finset.mem_union.mp (h2 hj2) with h | h <;> have := Finset.mem_Icc.mp h <;> omega
  have hassoc : ∀ i ∈ R₁, ∀ j ∈ R₁ ∪ R₂, i ≠ j →
      Associated (c i - c j) ((ℓ : ℤ_[ℓ]) ^ padicValInt ℓ (i - j)) := by
    intro i _ j _ hij
    obtain ⟨hne, hv⟩ := hc i j hij
    rw [← hv]
    exact assoc_pow_valuation hne
  have hI := Formalism.LIFT.lift_LagrangeIdealInt ℓ ℤ_[ℓ] R₁ R₂ c hdisj hassoc
  have hkill := kill_of_mem_span T _ _ _ x hI hx1 hx2
  have hle : (R₁.sup fun i => (∑ j ∈ R₂, padicValInt ℓ (i - j)) +
      ∑ j ∈ R₁.erase i, padicValInt ℓ (i - j)) ≤ E := by
    apply Finset.sup_le
    intro j₀ hj₀
    have := (gap_bound ℓ a S η b R₁ R₂ hab h1 h2 j₀ hj₀).trans hE
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm, mul_smul, hkill, smul_zero]

lemma valuation_prod {ℓ : ℕ} [Fact ℓ.Prime] (s : Finset ℤ) (f : ℤ → ℤ_[ℓ])
    (hf : ∀ j ∈ s, f j ≠ 0) :
    (∏ j ∈ s, f j) ≠ 0 ∧ PadicInt.valuation (∏ j ∈ s, f j) = ∑ j ∈ s, (f j).valuation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero hfa h1, by rw [PadicInt.valuation_mul hfa h1, h2]⟩

theorem rRVal_proof : RRVal := by
  intro ℓ _ c hc0 hc a S η b
  dsimp only
  set J := (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
    Finset.Icc (1 - ((b : ℤ) + S)) ((a : ℤ) - b)).erase 0 with hJ
  have hne : ∀ j ∈ J, c j ≠ 0 := by
    intro j hj
    have h0 := Finset.ne_of_mem_erase hj
    have := (hc j 0 h0).1
    rwa [hc0, sub_zero] at this
  have hv : ∀ j ∈ J, (c j).valuation = padicValInt ℓ j := by
    intro j hj
    have h0 := Finset.ne_of_mem_erase hj
    have := (hc j 0 h0).2
    rwa [hc0, sub_zero, sub_zero] at this
  obtain ⟨hp, hval⟩ := valuation_prod J c hne
  refine ⟨hp, ?_⟩
  rw [hval, Finset.sum_congr rfl hv,
    ← Finset.sum_filter_add_sum_filter_not J (fun j => 1 - (η : ℤ) ≤ j ∧ j ≤ η + a), Nat.cast_add]
  have hA := Formalism.WindowSums.arc_WindowSum ℓ (1 - (η : ℤ)) (a + 2 * η) (η + a)
    (J.filter fun j => 1 - (η : ℤ) ≤ j ∧ j ≤ η + a)
    (by
      intro j hj
      simp only [hJ, Finset.mem_filter, Finset.mem_erase, Finset.mem_union, Finset.mem_Icc] at hj
      rw [Finset.mem_Ico]; push_cast; omega)
    (by
      intro hj
      simp only [hJ, Finset.mem_filter, Finset.mem_erase] at hj
      exact hj.1.1 rfl)
    (by
      intro j hj
      simp only [hJ, Finset.mem_filter, Finset.mem_erase, Finset.mem_union, Finset.mem_Icc] at hj
      rw [abs_le]; push_cast; constructor <;> omega)
  have hB := Formalism.WindowSums.arc_WindowSum ℓ (1 - ((b : ℤ) + S)) (a + S) (b + S)
    (J.filter fun j => ¬ (1 - (η : ℤ) ≤ j ∧ j ≤ η + a))
    (by
      intro j hj
      simp only [hJ, Finset.mem_filter, Finset.mem_erase, Finset.mem_union, Finset.mem_Icc] at hj
      rw [Finset.mem_Ico]; push_cast; omega)
    (by
      intro hj
      simp only [hJ, Finset.mem_filter, Finset.mem_erase] at hj
      exact hj.1.1 rfl)
    (by
      intro j hj
      simp only [hJ, Finset.mem_filter, Finset.mem_erase, Finset.mem_union, Finset.mem_Icc] at hj
      rw [abs_le]; push_cast; constructor <;> omega)
  have hsum : ((a + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + ((a + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) =
      ((2 * a + 2 * η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) := by
    rw [← add_div]
    congr 1
    push_cast
    ring
  linarith

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

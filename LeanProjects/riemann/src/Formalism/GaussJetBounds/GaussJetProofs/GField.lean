import Formalism.GaussJetBounds.StatementM

noncomputable section
open scoped BigOperators NNReal

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section Gauss

variable {F : Type} [NormedField F] {σ : Type}

def gN (P : MvPolynomial σ F) : ℝ := ⨆ n : σ →₀ ℕ, ‖coeff n P‖

lemma gN_bdd (P : MvPolynomial σ F) : BddAbove (Set.range fun n : σ →₀ ℕ => ‖coeff n P‖) := by
  refine ⟨∑ n ∈ P.support, ‖coeff n P‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ∈ P.support
  · exact Finset.single_le_sum (f := fun n => ‖coeff n P‖) (fun _ _ => norm_nonneg _) hn
  · show ‖coeff n P‖ ≤ _
    rw [notMem_support_iff.mp hn, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma le_gN (P : MvPolynomial σ F) (n : σ →₀ ℕ) : ‖coeff n P‖ ≤ gN P :=
  le_ciSup (gN_bdd P) n

lemma gN_nonneg (P : MvPolynomial σ F) : 0 ≤ gN P := (norm_nonneg _).trans (le_gN P 0)

lemma gN_le {P : MvPolynomial σ F} {c : ℝ} (h : ∀ n, ‖coeff n P‖ ≤ c) : gN P ≤ c :=
  ciSup_le h

lemma gN_zero : gN (0 : MvPolynomial σ F) = 0 :=
  le_antisymm (gN_le fun n => by simp) (gN_nonneg _)

lemma gN_pos {P : MvPolynomial σ F} (hP : P ≠ 0) : 0 < gN P := by
  obtain ⟨n, hn⟩ := ne_zero_iff.mp hP
  exact (norm_pos_iff.mpr hn).trans_le (le_gN P n)

lemma gN_eq_zero {P : MvPolynomial σ F} : gN P = 0 ↔ P = 0 := by
  constructor
  · intro h
    by_contra hP
    exact (gN_pos hP).ne' h
  · rintro rfl
    exact gN_zero

lemma gN_C (z : F) : gN (C z : MvPolynomial σ F) = ‖z‖ := by
  classical
  apply le_antisymm
  · refine gN_le fun n => ?_
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · simp
  · simpa using le_gN (C z : MvPolynomial σ F) 0

lemma exists_min_gN [LinearOrder σ] {P : MvPolynomial σ F} (hP : P ≠ 0) :
    ∃ i : σ →₀ ℕ, ‖coeff i P‖ = gN P ∧ ∀ k : σ →₀ ℕ, toLex k < toLex i → ‖coeff k P‖ < gN P := by
  classical
  have hne : P.support.Nonempty := support_nonempty.mpr hP
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image P.support (fun n => ‖coeff n P‖) hne
  have hmg : ‖coeff m P‖ = gN P := by
    refine le_antisymm (le_gN P m) (gN_le fun n => ?_)
    by_cases hn : n ∈ P.support
    · exact hmax n hn
    · rw [notMem_support_iff.mp hn, norm_zero]
      exact norm_nonneg _
  let S := P.support.filter fun n => ‖coeff n P‖ = gN P
  have hS : S.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨hm, hmg⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S (fun n => toLex n) hS
  refine ⟨i, (Finset.mem_filter.mp hi).2, fun k hk => lt_of_le_of_ne (le_gN P k) fun hkg => ?_⟩
  have hkS : k ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, hkg⟩
    rw [mem_support_iff]
    intro h0
    rw [h0, norm_zero] at hkg
    exact (gN_pos hP).ne hkg
  exact absurd (hmin k hkS) (not_le.mpr hk)

variable [IsUltrametricDist F]

lemma gN_add_le (P Q : MvPolynomial σ F) : gN (P + Q) ≤ max (gN P) (gN Q) := by
  refine gN_le fun n => ?_
  rw [coeff_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (le_gN P n) (le_gN Q n))

lemma gN_mul_le (P Q : MvPolynomial σ F) : gN (P * Q) ≤ gN P * gN Q := by
  classical
  refine gN_le fun n => ?_
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (gN_nonneg P) (gN_nonneg Q)) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_gN P _) (le_gN Q _) (norm_nonneg _) (gN_nonneg P)

lemma gN_mul (P Q : MvPolynomial σ F) : gN (P * Q) = gN P * gN Q := by
  classical
  by_cases hP : P = 0
  · simp [hP, gN_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gN_zero]
  refine le_antisymm (gN_mul_le P Q) ?_
  obtain ⟨_, _⟩ := exists_wellFoundedLT σ
  obtain ⟨i, hi, hi'⟩ := exists_min_gN hP
  obtain ⟨j, hj, hj'⟩ := exists_min_gN hQ
  have key : ‖coeff (i + j) (P * Q)‖ = ‖coeff i P * coeff j Q‖ := by
    rw [coeff_mul]
    refine IsNonarchimedean.apply_sum_eq_of_lt (f := fun x : F => ‖x‖)
      (l := fun p : (σ →₀ ℕ) × (σ →₀ ℕ) => coeff p.1 P * coeff p.2 Q) (k := (i, j))
      IsUltrametricDist.isNonarchimedean_norm (fun a => (norm_neg a).symm)
      (by simp) ?_
    rintro ⟨a, b⟩ hab hne
    replace hab : a + b = i + j := by simpa using hab
    simp only [norm_mul, hi, hj]
    have hcase : toLex a < toLex i ∨ toLex b < toLex j := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hsum : toLex a + toLex b = toLex i + toLex j := by
        rw [← toLex_add, ← toLex_add]
        exact congrArg toLex hab
      rcases h1.lt_or_eq with h1 | h1
      · exact absurd hsum (add_lt_add_of_lt_of_le h1 h2).ne'
      rcases h2.lt_or_eq with h2 | h2
      · exact absurd hsum (add_lt_add_of_le_of_lt h1.le h2).ne'
      exact hne (Prod.ext (toLex.injective h1.symm) (toLex.injective h2.symm))
    rcases hcase with h | h
    · exact (mul_le_mul_of_nonneg_left (le_gN Q b) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_right (hi' a h) (gN_pos hQ))
    · exact (mul_le_mul_of_nonneg_right (le_gN P a) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left (hj' b h) (gN_pos hP))
  calc gN P * gN Q = ‖coeff i P * coeff j Q‖ := by rw [norm_mul, hi, hj]
    _ = ‖coeff (i + j) (P * Q)‖ := key.symm
    _ ≤ gN (P * Q) := le_gN _ _

def gNN (P : MvPolynomial σ F) : ℝ≥0 := Real.toNNReal (gN P)

omit [IsUltrametricDist F] in
lemma coe_gNN (P : MvPolynomial σ F) : ((gNN P : ℝ≥0) : ℝ) = gN P :=
  Real.coe_toNNReal _ (gN_nonneg P)

def gVal (F σ : Type) [NormedField F] [IsUltrametricDist F] : Valuation (MvPolynomial σ F) ℝ≥0 where
  toFun P := gNN P
  map_zero' := by
    apply NNReal.coe_injective
    rw [coe_gNN, gN_zero, NNReal.coe_zero]
  map_one' := by
    apply NNReal.coe_injective
    have := gN_C (σ := σ) (1 : F)
    rw [coe_gNN, NNReal.coe_one]
    simpa using this
  map_mul' P Q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, coe_gNN, coe_gNN, coe_gNN, gN_mul]
  map_add_le_max' P Q := by
    rw [← NNReal.coe_le_coe, NNReal.coe_max, coe_gNN, coe_gNN, coe_gNN]
    exact gN_add_le P Q

lemma gVal_coe (P : MvPolynomial σ F) : ((gVal F σ P : ℝ≥0) : ℝ) = gN P := coe_gNN P

lemma gVal_supp : nonZeroDivisors (MvPolynomial σ F) ≤ (gVal F σ).supp.primeCompl := by
  intro P hP hmem
  rw [SetLike.mem_coe, Valuation.mem_supp_iff] at hmem
  have h0 : gN P = 0 := by rw [← gVal_coe, hmem]; rfl
  exact nonZeroDivisors.ne_zero hP (gN_eq_zero.mp h0)

abbrev GK (F σ : Type) [NormedField F] : Type := FractionRing (MvPolynomial σ F)

def gValK (F σ : Type) [NormedField F] [IsUltrametricDist F] : Valuation (GK F σ) ℝ≥0 :=
  (gVal F σ).extendToLocalization gVal_supp (GK F σ)

lemma gValK_algebraMap (P : MvPolynomial σ F) :
    ((gValK F σ (algebraMap _ (GK F σ) P) : ℝ≥0) : ℝ) = gN P := by
  rw [gValK, Valuation.extendToLocalization_apply_map_apply, gVal_coe]

def gAbs (F σ : Type) [NormedField F] [IsUltrametricDist F] : AbsoluteValue (GK F σ) ℝ where
  toFun x := (gValK F σ x : ℝ≥0)
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by simp
  add_le' x y := by
    have h := (gValK F σ).map_add x y
    rw [← NNReal.coe_le_coe, NNReal.coe_max] at h
    exact h.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

lemma gAbs_add_le_max (x y : GK F σ) : gAbs F σ (x + y) ≤ max (gAbs F σ x) (gAbs F σ y) := by
  have h := (gValK F σ).map_add x y
  rw [← NNReal.coe_le_coe, NNReal.coe_max] at h
  exact h

lemma gAbs_algebraMap (P : MvPolynomial σ F) : gAbs F σ (algebraMap _ (GK F σ) P) = gN P :=
  gValK_algebraMap P

end Gauss

lemma norm_intCast_padicComplex (l : ℕ) [Fact l.Prime] (z : ℤ) :
    ‖(z : ℂ_[l])‖ = ‖(z : ℚ_[l])‖ := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']

lemma gN_map_int (l : ℕ) [Fact l.Prime] {σ : Type} (P : MvPolynomial σ ℤ)
    (hP : MvPolynomial.map (Int.castRingHom (ZMod l)) P ≠ 0) :
    gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) = 1 := by
  apply le_antisymm
  · refine gN_le fun n => ?_
    rw [coeff_map, eq_intCast, norm_intCast_padicComplex]
    exact Padic.norm_int_le_one _
  · obtain ⟨n, hn⟩ := ne_zero_iff.mp hP
    rw [coeff_map, eq_intCast] at hn
    have hnd : ¬ (l : ℤ) ∣ coeff n P := fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
    have h1 : ‖((coeff n P : ℤ) : ℚ_[l])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one _)
        (not_lt.mp fun h => hnd (Padic.norm_intCast_lt_one_iff.mp h))
    have := le_gN (MvPolynomial.map (Int.castRingHom ℂ_[l]) P) n
    rwa [coeff_map, eq_intCast, norm_intCast_padicComplex, h1] at this

lemma eval₂_ringHom_eq {σ A K : Type} [CommRing A] [CommRing K] (ι : MvPolynomial σ A →+* K)
    (P : MvPolynomial σ A) : eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := by
  have := eval₂_comp_left ι (C : A →+* MvPolynomial σ A) X P
  rw [eval₂_eta] at this
  exact this.symm

lemma aeval_int_eq {σ A K : Type} [CommRing A] [CommRing K] [Algebra ℤ K]
    (ι : MvPolynomial σ A →+* K) (P : MvPolynomial σ ℤ) :
    aeval (fun i => ι (X i)) P = ι (MvPolynomial.map (Int.castRingHom A) P) := by
  rw [aeval_def, ← eval₂_ringHom_eq, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem residuallyGenericExists : GenericExists := by
  intro l _ σ _
  let inst : NormedField (GK ℂ_[l] σ) := (gAbs ℂ_[l] σ).toNormedField
  let ι : MvPolynomial σ ℂ_[l] →+* GK ℂ_[l] σ := algebraMap _ _
  have hι : ∀ P, ‖ι P‖ = gN P := fun P => gAbs_algebraMap P
  have hev : ∀ P, eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := eval₂_ringHom_eq ι
  refine ⟨GK ℂ_[l] σ, inst, ?_, ?_, ι.comp C, fun i => ι (X i), ?_, ?_, ?_⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      fun x y => gAbs_add_le_max x y
  · exact charZero_of_injective_ringHom (ι.comp C).injective
  · intro z
    rw [RingHom.comp_apply, hι, gN_C]
  · intro P
    rw [hev, hι]
    rfl
  · intro P hP
    refine (congrArg norm (@aeval_int_eq σ ℂ_[l] (GK ℂ_[l] σ) _ _ (Ring.toIntAlgebra _) ι P)).trans ?_
    rw [hι]
    exact gN_map_int l P hP

end Formalism.DworkPowerSeriesWeights

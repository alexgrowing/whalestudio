import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCorePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangePf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsUnitEvalOfMapResidueNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ResidueNormValuationSubringEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SummableNormBoundedSeries

namespace GlobalTheory.DiscEval

open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries

section Series

variable {K : Type*} [NormedField K] [CompleteSpace K] {O : Type*} [CommRing O]
  (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) {t : K} (ht : ‖t‖ < 1)

omit [CompleteSpace K] in
include hi ht in
theorem summable_norm_term (f : O⟦X⟧) :
    Summable fun n : ℕ => ‖i (PowerSeries.coeff n f) * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg t) ht)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hi _)

noncomputable def discEval : O⟦X⟧ →+* K :=
  GlobalTheory.BoundedPowerSeriesDisc.evalDisc i hi t ht

theorem hasSum_discEval (f : O⟦X⟧) :
    HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) :=
  (summable_norm_term i hi ht f).of_norm.hasSum

@[simp] theorem discEval_C (a : O) : discEval i hi ht (PowerSeries.C a) = i a := by
  refine (hasSum_discEval i hi ht _).unique ?_
  convert hasSum_single 0 fun n hn => ?_ using 1
  · simp
  · simp [PowerSeries.coeff_C, hn]

@[simp] theorem discEval_X : discEval i hi ht PowerSeries.X = t := by
  refine (hasSum_discEval i hi ht _).unique ?_
  convert hasSum_single 1 fun n hn => ?_ using 1
  · simp
  · simp [PowerSeries.coeff_X, hn]

theorem norm_discEval_le_one [IsUltrametricDist K] (f : O⟦X⟧) : ‖discEval i hi ht f‖ ≤ 1 := by
  rw [← (hasSum_discEval i hi ht f).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hi _) (by positivity) (pow_le_one₀ (norm_nonneg _) ht.le)

theorem norm_discEval_sub_le [IsUltrametricDist K] (f : O⟦X⟧) :
    ‖discEval i hi ht f - i (PowerSeries.constantCoeff f)‖ ≤ ‖t‖ := by
  have h := congrArg (discEval i hi ht) (PowerSeries.eq_X_mul_shift_add_const f)
  rw [map_add, map_mul, discEval_X, discEval_C] at h
  rw [h, add_sub_cancel_right, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_discEval_le_one i hi ht _)

theorem discEval_mem {B : Subring K} (hB : IsClosed (B : Set K)) (hiB : ∀ x, i x ∈ B)
    (htB : t ∈ B) (f : O⟦X⟧) : discEval i hi ht f ∈ B :=
  hB.mem_of_tendsto (hasSum_discEval i hi ht f) (Eventually.of_forall fun _ =>
    B.sum_mem fun _ _ => B.mul_mem (hiB _) (B.pow_mem htB _))

end Series

section Away

variable {K : Type*} {O : Type*} [CommRing O] (π : O)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

section Laurent

variable [Field K] (i : O →+* K) (hπ : i π ≠ 0)

noncomputable def laurent : A →+* K⸨X⸩ :=
  IsLocalization.Away.lift (PowerSeries.C π * PowerSeries.X : O⟦X⟧)
    (g := (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i)) (by
      rw [isUnit_iff_ne_zero, RingHom.comp_apply,
        map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_mul, PowerSeries.map_C,
        PowerSeries.map_X]
      exact mul_ne_zero (by simpa using hπ) PowerSeries.X_ne_zero)

@[simp] theorem laurent_algebraMap (f : O⟦X⟧) :
    laurent π A i hπ (algebraMap O⟦X⟧ A f) = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map i f) :=
  IsLocalization.Away.lift_eq _ _ f

variable {π A}

theorem coeff_laurent {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀)
    (n : ℤ) : (laurent π A i hπ f).coeff n =
      if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀) := by
  have h1 := congrArg (laurent π A i hπ) h
  rw [map_mul, laurent_algebraMap, laurent_algebraMap] at h1
  have h2 : HahnSeries.ofPowerSeries ℤ K (PowerSeries.map i
      (PowerSeries.C π ^ a * PowerSeries.X ^ b)) = HahnSeries.single (b : ℤ) (i π ^ a) := by
    rw [map_mul, map_pow, map_pow, PowerSeries.map_C, PowerSeries.map_X,
      ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow,
      HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h3 := congrArg (fun g : K⸨X⸩ => g.coeff (n + b)) h1
  simp only [h2, HahnSeries.coeff_mul_single_add] at h3
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
  have h4 : i π ^ a ≠ 0 := pow_ne_zero _ hπ
  split_ifs at h3 ⊢
  · exact (mul_eq_zero.1 h3).resolve_right h4
  · rw [← h3, inv_pow]
    field_simp

end Laurent

theorem exists_mul_eq (f : A) : ∃ (a b : ℕ) (f₀ : O⟦X⟧),
    f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ := by
  obtain ⟨k, f₀, h⟩ := IsLocalization.Away.surj (PowerSeries.C π * PowerSeries.X : O⟦X⟧) f
  exact ⟨k, k, f₀, by rw [← mul_pow, map_pow, h]⟩

section Value

variable [NormedField K] [CompleteSpace K] (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)

noncomputable def discEvalAway : A →+* K :=
  IsLocalization.Away.lift (PowerSeries.C π * PowerSeries.X : O⟦X⟧) (g := discEval i hi ht) (by
    rw [isUnit_iff_ne_zero, map_mul, discEval_C, discEval_X]
    exact mul_ne_zero hπ ht0)

@[simp] theorem discEvalAway_algebraMap (f : O⟦X⟧) :
    discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f :=
  IsLocalization.Away.lift_eq _ _ f

variable {π A}

theorem discEvalAway_eq {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀) :
    discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ := by
  have h1 := congrArg (discEvalAway π A i hi hπ ht0 ht) h
  simp only [map_mul, discEvalAway_algebraMap, map_pow, discEval_C, discEval_X] at h1
  rw [← h1, inv_pow, inv_pow]
  field_simp

theorem hasSum_laurent (f : A) :
    HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
      (discEvalAway π A i hi hπ ht0 ht f) := by
  obtain ⟨a, b, f₀, h⟩ := exists_mul_eq π A f
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - b := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff, discEvalAway_eq i hi hπ ht0 ht h]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval i hi ht f₀).mul_left ((i π)⁻¹ ^ a * t⁻¹ ^ b))
    rw [Function.comp_apply, coeff_laurent i hπ h, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, inv_pow t]
    ring
  · intro n hn
    rw [coeff_laurent i hπ h, if_pos, zero_mul]
    by_contra h0
    exact hn ⟨(n + b).toNat, by simp only; omega⟩

include hi ht0 ht in

theorem tendsto_norm_laurent_term (f : A) :
    Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) := by
  simpa using (hasSum_laurent i hi hπ ht0 ht f).summable.tendsto_cofinite_zero.norm

theorem discEvalAway_mem {B : Subfield K} (hB : IsClosed (B : Set K)) (hiB : ∀ x, i x ∈ B)
    (htB : t ∈ B) (f : A) : discEvalAway π A i hi hπ ht0 ht f ∈ B := by
  obtain ⟨a, b, f₀, h⟩ := exists_mul_eq π A f
  rw [discEvalAway_eq i hi hπ ht0 ht h]
  exact B.mul_mem (B.mul_mem (B.pow_mem (B.inv_mem (hiB π)) a) (B.pow_mem (B.inv_mem htB) b))
    (discEval_mem i hi ht (B := B.toSubring) hB hiB htB f₀)

end Value

end Away

section Coefficients

open MvPolynomial

variable {K : Type*} [Field K] {σ τ : Type*}

noncomputable def coeffPoly (m : ℤ) (G : MvPolynomial σ K⸨X⸩) : MvPolynomial σ K :=
  ∑ μ ∈ G.support, monomial μ ((coeff μ G).coeff m)

@[simp] theorem coeff_coeffPoly (m : ℤ) (G : MvPolynomial σ K⸨X⸩) (μ : σ →₀ ℕ) :
    coeff μ (coeffPoly m G) = (coeff μ G).coeff m := by
  classical
  simp only [coeffPoly, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [notMem_support_iff.1 h]

theorem coeffPoly_sum {α : Type*} (m : ℤ) (s : Finset α) (G : α → MvPolynomial σ K⸨X⸩) :
    coeffPoly m (∑ a ∈ s, G a) = ∑ a ∈ s, coeffPoly m (G a) := by
  ext μ
  simp [coeff_sum, HahnSeries.coeff_sum]

theorem coeffPoly_C_mul_map (m : ℤ) (c : K⸨X⸩) (Q : MvPolynomial σ K) :
    coeffPoly m (C c * map (HahnSeries.C : K →+* K⸨X⸩) Q) = C (c.coeff m) * Q := by
  ext μ
  rw [coeff_coeffPoly, coeff_C_mul, coeff_C_mul, coeff_map, HahnSeries.C_apply,
    HahnSeries.coeff_mul_single_zero]

theorem coeffPoly_bind₁ (m : ℤ) (g : σ → MvPolynomial τ K) (G : MvPolynomial σ K⸨X⸩) :
    coeffPoly m (bind₁ (fun k => map (HahnSeries.C : K →+* K⸨X⸩) (g k)) G) =
      bind₁ g (coeffPoly m G) := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum, coeffPoly_sum, coeffPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [bind₁_monomial, bind₁_monomial, ← coeffPoly_C_mul_map, map_prod]
  simp only [map_pow]

theorem isHomogeneous_coeffPoly (m : ℤ) {G : MvPolynomial σ K⸨X⸩} {d : ℕ}
    (hG : G.IsHomogeneous d) : (coeffPoly m G).IsHomogeneous d := fun μ hμ =>
  hG fun h => hμ (by rw [coeff_coeffPoly, h, HahnSeries.coeff_zero])

theorem exists_coeffPoly_eq_zero (G : MvPolynomial σ K⸨X⸩) :
    ∃ b : ℕ, ∀ m : ℤ, m < -(b : ℤ) → coeffPoly m G = 0 := by
  refine ⟨G.support.sup fun μ => (-(coeff μ G).order).toNat, fun m hm => ?_⟩
  ext μ
  rw [coeff_coeffPoly, coeff_zero]
  by_cases h : μ ∈ G.support
  · have := Finset.le_sup (f := fun μ => (-(coeff μ G).order).toNat) h
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  · simp [notMem_support_iff.1 h]

end Coefficients

section Core

open MvPolynomial

variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

theorem hasSum_coeffPoly {K : Type*} [NormedField K] [CompleteSpace K] (i : O →+* K)
    (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1) {σ : Type*}
    (F : MvPolynomial σ A) (x : σ → K) :
    HasSum (fun m : ℤ => eval x (coeffPoly m (map (laurent π A i hπ) F)) * t ^ m)
      (eval₂ (discEvalAway π A i hi hπ ht0 ht) x F) := by
  have h : ∀ m : ℤ, coeffPoly m (map (laurent π A i hπ) F) =
      ∑ μ ∈ F.support, monomial μ ((laurent π A i hπ (coeff μ F)).coeff m) := fun m => by
    classical
    ext μ
    simp only [coeff_coeffPoly, coeff_map, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp [notMem_support_iff.1 h]
  rw [eval₂_eq]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ F.support) =>
      (hasSum_laurent i hi hπ ht0 ht (coeff μ F)).mul_right (∏ k ∈ μ.support, x k ^ μ k))
  rw [h, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [eval_monomial, Finsupp.prod]
  ring

theorem norm_coeff_bind₁_le {K : Type*} [NormedField K] [IsUltrametricDist K] {σ τ : Type*}
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) (hP1 : ∀ μ, ‖coeff μ P‖ ≤ 1)
    {g : σ → MvPolynomial τ K} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ k μ, ‖coeff μ (g k)‖ ≤ c)
    (μ : τ →₀ ℕ) : ‖coeff μ (bind₁ g P)‖ ≤ c ^ d := by
  open ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.BasisChangePf in
  have hmain : CB (bind₁ g P) (c ^ d) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hc d) fun ν hν => ?_
    rw [bind₁_monomial]
    have hdeg : ∑ k ∈ ν.support, ν k = d := by
      have := hP (mem_support_iff.1 hν)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have h1 := cb_C_mul (coeff ν P) (cb_prod ν.support _ (fun k => c ^ ν k)
      (fun k => pow_nonneg hc _) (fun k _ => cb_pow hc (hg k) (ν k)))
    rw [Finset.prod_pow_eq_pow_sum, hdeg] at h1
    exact fun μ' => (h1 μ').trans (mul_le_of_le_one_left (pow_nonneg hc d) (hP1 ν))
  exact hmain μ

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_detProdPoly_le {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] (μ : EntryIndex n n →₀ ℕ) : ‖coeff μ (detProdPoly K n)‖ ≤ 1 := by
  have h : map (Int.castRingHom K) (detProdPoly ℤ n) = detProdPoly K n := by
    rw [detProdPoly, detProdPoly, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i j : 2
    simp
  rw [← h, coeff_map]
  exact IsUltrametricDist.norm_intCast_le_one K _

theorem exists_norm_coeff_detProdPoly {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : ∃ μ, ‖coeff μ (detProdPoly K n)‖ = 1 := by
  by_contra! h
  have h1 : eval (entries fun s => (1 : Matrix (n s) (n s) K)) (detProdPoly K n) = 1 := by
    simp [eval_detProdPoly]
  have h2 : ‖eval (entries fun s => (1 : Matrix (n s) (n s) K)) (detProdPoly K n)‖ < 1 := by
    rw [eval_eq]
    refine norm_lt_of_hasSum one_pos (Finset.hasSum _ _) fun μ => ?_
    rw [Function.comp_apply, norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt
      ((norm_coeff_detProdPoly_le n _).lt_of_ne (h _))
    rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    simp only [entries, Matrix.one_apply]
    split_ifs <;> simp
  simp [h1] at h2

variable [CompleteSpace K]

theorem coeffPoly_integral_of_admissible (K₀ : Subfield K)
    (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (S : Set K)
    (hS : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1)
    (hdense : ∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε)
    (hrot : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S)
    (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {σ : Type} [Fintype σ]
    (δ : MvPolynomial σ K) (hδ : ∀ μ, ‖coeff μ δ‖ ≤ 1) (hδ1 : ∃ μ, ‖coeff μ δ‖ = 1)
    (F : MvPolynomial σ A)
    (hF : ∀ t ∈ S, ∀ (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (x : σ → K), (∀ k, x k ∈ K₀ ∧ ‖x k‖ ≤ 1) →
      ‖eval x δ‖ = 1 → ‖eval₂ (discEvalAway π A i hi hπ ht0 ht) x F‖ ≤ 1) (m : ℤ) :
    (∀ μ, ‖coeff μ (coeffPoly m (map (laurent π A i hπ) F))‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by
  obtain ⟨b, hb⟩ := exists_coeffPoly_eq_zero (map (laurent π A i hπ) F)
  refine ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finCore_holds K K₀ hres S hS hdense hrot σ δ hδ hδ1 _ b hb
    (fun t htS x hx hxδ => ?_) m
  have ht0 := norm_pos_iff.1 (hS t htS).1
  have h := hasSum_coeffPoly i hi hπ ht0 (hS t htS).2 F x
  refine ⟨by simpa using h.summable.tendsto_cofinite_zero.norm, ?_⟩
  rw [h.tsum_eq]
  exact hF t htS ht0 _ x hx hxδ

end Core

section Padic

theorem exists_comp_eq_of_mem_range {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    (e : B →+* K) (he : Function.Injective e) (φ : R →+* K) (h : ∀ a, φ a ∈ e.range) :
    ∃ ψ : R →+* B, ∀ a, e (ψ a) = φ a := by
  let ε : B ≃+* e.range := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun a b hab => he (congrArg Subtype.val hab), e.rangeRestrict_surjective⟩
  exact ⟨ε.symm.toRingHom.comp (φ.codRestrict e.range h), fun a =>
    congrArg Subtype.val (ε.apply_symm_apply ⟨φ a, h a⟩)⟩

theorem residueFieldInfiniteOn_fieldRange {C K : Type*} [NormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [NormedField K] [IsUltrametricDist K] (e : C →+* K) (he : ∀ x, ‖e x‖ = ‖x‖) :
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (e.fieldRange : Set K) := by
  intro s
  by_contra! h
  have := infinite_residueField_of_isAlgClosed (C := C)
  choose l hl using fun a => residue_surjective
    (R := (NormedField.valuation (K := C)).valuationSubring) a
  choose y hy hy1 using fun a => h (e (l a)) ⟨l a, rfl⟩
    (by rw [he]; exact (mem_normValuationSubring_iff _).1 (l a).2)
  obtain ⟨a, b, hab, h1⟩ := Finite.exists_ne_map_eq_of_infinite fun a => (⟨y a, hy a⟩ : s)
  have h2 : y a = y b := congrArg Subtype.val h1
  refine hab ?_
  rw [← hl a, ← hl b, ← sub_eq_zero, ← map_sub, residue_normValuationSubring_eq_zero_iff, ← he]
  have : e ((l a - l b : (NormedField.valuation (K := C)).valuationSubring) : C) =
      (e (l a) - y a) + -(e (l b) - y b) := by
    rw [h2]
    simp
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt (hy1 a) (by rw [norm_neg]; exact hy1 b))

theorem exists_abs_norm_sub_lt {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {r ε : ℝ}
    (h0 : 0 < r) (h1 : r < 1) (hε : 0 < ε) : ∃ x : C, 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ |‖x‖ - r| < ε := by
  obtain ⟨x, hx, hx1⟩ := exists_lt_norm_lt_one_of_isAlgClosed (C := C) (max 0 (1 - ε))
    (max_lt one_pos (by linarith))
  rw [max_lt_iff] at hx
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one h0 h1.le hx.1 hx1
  have h2 : ‖x‖ ^ n ≤ 1 := pow_le_one₀ hx.1.le hx1.le
  refine ⟨x ^ (n + 1), by rw [norm_pow]; exact pow_pos hx.1 _, by rw [norm_pow]; linarith, ?_⟩
  rw [norm_pow, abs_lt]
  rw [pow_succ] at hn ⊢
  constructor <;> nlinarith

variable (p : ℕ) [Fact p.Prime]

noncomputable def algField : Subfield ℂ_[p] := (algebraMap (PadicAlgCl p) ℂ_[p]).fieldRange

def algDisc : Set ℂ_[p] := {t | t ∈ algField p ∧ 0 < ‖t‖ ∧ ‖t‖ < 1}

theorem residueFieldInfiniteOn_algField :
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (algField p : Set ℂ_[p]) :=
  residueFieldInfiniteOn_fieldRange _ (PadicComplex.norm_extends p)

theorem algDisc_dense (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ algDisc p, |‖t‖ - r| < ε := by
  obtain ⟨x, hx0, hx1, hx⟩ := exists_abs_norm_sub_lt (C := PadicAlgCl p) h0 h1 hε
  rw [← PadicComplex.norm_extends] at hx0 hx1 hx
  exact ⟨x, ⟨⟨x, rfl⟩, hx0, hx1⟩, hx⟩

theorem mul_mem_algDisc (t : ℂ_[p]) (ht : t ∈ algDisc p) (τ : ℂ_[p]) (hτ : τ ∈ algField p)
    (hτ1 : ‖τ‖ = 1) : t * τ ∈ algDisc p :=
  ⟨mul_mem ht.1 hτ, by rw [norm_mul, hτ1, mul_one]; exact ht.2⟩

variable {p}

theorem mem_algField_iff {x : ℂ_[p]} : x ∈ algField p ↔ IsIntegral ℚ_[p] x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).algebraMap
  · intro hx
    have h : IsIntegral (PadicAlgCl p) x := hx.tower_top
    exact minpoly.mem_range_of_degree_eq_one _ _
      (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h))

theorem ringHom_padicInt_eq (g : ℤ_[p] →+* ℂ_[p]) (hg : ∀ z, ‖g z‖ ≤ 1) (z : ℤ_[p]) :
    g z = algebraMap ℚ_[p] ℂ_[p] z := by
  let h : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hh : ∀ z, ‖h z‖ ≤ 1 := fun z => by
    change ‖algebraMap ℚ_[p] ℂ_[p] z‖ ≤ 1
    rw [norm_algebraMap']
    exact z.2
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have key : ∀ n : ℕ, ‖g z - h z‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun n => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = y * p ^ n + (z.appr n : ℕ) := by rw [hy]; ring
    have : g z - h z = (g y + -h y) * p ^ n := by
      conv_lhs => rw [hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hg y) (by rw [norm_neg]; exact hh y)))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

noncomputable def fieldEmb (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : L →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap L (PadicAlgCl p))

noncomputable def intEmb (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    integralClosure ℤ_[p] L →+* ℂ_[p] :=
  (fieldEmb L).comp (algebraMap (integralClosure ℤ_[p] L) L)

section Field

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem fieldEmb_apply (x : L) : fieldEmb L x = ((x : PadicAlgCl p) : ℂ_[p]) := rfl

theorem intEmb_apply (x : integralClosure ℤ_[p] L) : intEmb L x = fieldEmb L x := rfl

theorem intEmb_injective : Function.Injective (intEmb L) :=
  (fieldEmb L).injective.comp Subtype.val_injective

theorem fieldEmb_mem_algField (x : L) : fieldEmb L x ∈ algField p := ⟨x, rfl⟩

theorem mem_integralClosure_iff_norm (x : L) : x ∈ integralClosure ℤ_[p] L ↔ ‖fieldEmb L x‖ ≤ 1 := by
  rw [mem_integralClosure_padicInt_iff, fieldEmb_apply, PadicComplex.norm_extends]

theorem norm_intEmb_le_one (x : integralClosure ℤ_[p] L) : ‖intEmb L x‖ ≤ 1 :=
  (mem_integralClosure_iff_norm L x).1 x.2

theorem mem_range_intEmb_iff (x : ℂ_[p]) :
    x ∈ (intEmb L).range ↔ x ∈ (fieldEmb L).fieldRange ∧ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, rfl⟩, norm_intEmb_le_one L y⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨⟨y, (mem_integralClosure_iff_norm L y).2 hy⟩, rfl⟩

variable [FiniteDimensional ℚ_[p] L]

theorem mem_maximalIdeal_iff_norm (x : integralClosure ℤ_[p] L) :
    x ∈ maximalIdeal (integralClosure ℤ_[p] L) ↔ ‖intEmb L x‖ < 1 := by
  rw [mem_maximalIdeal_integralClosure_iff, intEmb_apply, fieldEmb_apply, PadicComplex.norm_extends]

theorem isUnit_iff_norm (x : integralClosure ℤ_[p] L) : IsUnit x ↔ ‖intEmb L x‖ = 1 := by
  rw [← notMem_maximalIdeal, mem_maximalIdeal_iff_norm, not_lt]
  exact ⟨fun h => le_antisymm (norm_intEmb_le_one L x) h, fun h => h.ge⟩

theorem isClosed_fieldRange : IsClosed ((fieldEmb L).fieldRange : Set ℂ_[p]) :=
  (LinearMap.range ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp
    L.val).toLinearMap).closed_of_finiteDimensional

theorem isAdicComplete_integralClosure :
    IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] L)) (integralClosure ℤ_[p] L) := by
  set S := integralClosure ℤ_[p] L
  set J := (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)
  have : IsAdicComplete J S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := ℤ_[p]) S
  have hJ : J ≤ maximalIdeal S :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[p]) S _ inferInstance
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ J := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := ℤ_[p]) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have he' : ∀ n, maximalIdeal S ^ ((e + 1) * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right e.le_succ).trans he) n
  have : IsPrecomplete (maximalIdeal S) S := ⟨fun u hu => by
    obtain ⟨l, hl⟩ := IsPrecomplete.prec' (I := J) (fun n => u ((e + 1) * n)) fun {m n} hmn =>
      (hu (Nat.mul_le_mul_left _ hmn)).mono (Submodule.smul_mono_left (he' m))
    exact ⟨l, fun n => (hu (Nat.le_mul_of_pos_left n e.succ_pos)).trans
      ((hl n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJ n)))⟩⟩
  exact ⟨⟩

theorem finite_residueField_integralClosure :
    Finite (ResidueField (integralClosure ℤ_[p] L)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[p] ℚ_[p] L
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[p] L
  have : Finite (ResidueField ℤ_[p]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[p])

end Field

section Finite

variable {O : Type*} [CommRing O] [Algebra ℤ_[p] O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1)

include hi in

theorem map_algebraMap_padicInt (z : ℤ_[p]) :
    i (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] ℂ_[p] z :=
  ringHom_padicInt_eq (i.comp (algebraMap ℤ_[p] O)) (fun _ => hi _) z

noncomputable def genField (T : Set ℂ_[p]) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {y : PadicAlgCl p | (y : ℂ_[p]) ∈ Set.range i ∪ T}

variable [Module.Finite ℤ_[p] O]

include hi

theorem map_mem_algField (x : O) : i x ∈ algField p := by
  obtain ⟨q, hq, hqx⟩ : IsIntegral ℤ_[p] x := Algebra.IsIntegral.isIntegral x
  refine mem_algField_iff.2 ⟨q.map (algebraMap ℤ_[p] ℚ_[p]), hq.map _, ?_⟩
  have h : (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p]) = i.comp (algebraMap ℤ_[p] O) :=
    RingHom.ext fun z => (map_algebraMap_padicInt i hi z).symm
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hqx, map_zero]

theorem fieldRange_genField {T : Set ℂ_[p]} (hT : T ⊆ algField p) :
    (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) := by
  refine le_antisymm ?_ (Subfield.closure_le.2 fun x hx => ?_)
  · rintro _ ⟨⟨y, hy⟩, rfl⟩
    change algebraMap (PadicAlgCl p) ℂ_[p] y ∈ _
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy => exact Subfield.subset_closure hy
    | algebraMap z =>
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) z
      rw [← IsScalarTower.algebraMap_apply, map_div₀]
      exact div_mem (Subfield.subset_closure (Or.inl ⟨_, map_algebraMap_padicInt i hi a⟩))
        (Subfield.subset_closure (Or.inl ⟨_, map_algebraMap_padicInt i hi b⟩))
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  · obtain ⟨y, rfl⟩ : x ∈ algField p := by
      rcases hx with ⟨a, rfl⟩ | hx
      exacts [map_mem_algField i hi a, hT hx]
    exact ⟨⟨y, IntermediateField.subset_adjoin _ _ hx⟩, rfl⟩

theorem map_mem_genField {T : Set ℂ_[p]} (hT : T ⊆ algField p) (x : O) :
    i x ∈ (fieldEmb (genField i T)).fieldRange := by
  rw [fieldRange_genField i hi hT]
  exact Subfield.subset_closure (Or.inl ⟨x, rfl⟩)

theorem mem_genField_of_mem {T : Set ℂ_[p]} (hT : T ⊆ algField p) {x : ℂ_[p]} (hx : x ∈ T) :
    x ∈ (fieldEmb (genField i T)).fieldRange := by
  rw [fieldRange_genField i hi hT]
  exact Subfield.subset_closure (Or.inr hx)

theorem finiteDimensional_genField {T : Set ℂ_[p]} (hT : T.Finite) :
    FiniteDimensional ℚ_[p] (genField i T) := by
  have hinj := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  obtain ⟨i₀, hi₀⟩ := exists_comp_eq_of_mem_range _ hinj i (map_mem_algField i hi)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := O)
  set U : Set (PadicAlgCl p) := i₀ '' s ∪ algebraMap (PadicAlgCl p) ℂ_[p] ⁻¹' T
  have : Finite U := ((s.finite_toSet.image _).union (hT.preimage hinj.injOn)).to_subtype
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] U) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ b, i₀ b ∈ IntermediateField.adjoin ℚ_[p] U := fun b => by
    have hb : b ∈ Submodule.span ℤ_[p] (s : Set O) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      have : i₀ (algebraMap ℤ_[p] O a) = algebraMap ℚ_[p] (PadicAlgCl p) a := hinj (by
        rw [hi₀, map_algebraMap_padicInt i hi, ← IsScalarTower.algebraMap_apply])
      rw [Algebra.smul_def, map_mul, this]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
  have hle : genField i T ≤ IntermediateField.adjoin ℚ_[p] U := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro y (⟨a, ha⟩ | hy)
    · rw [← hinj ((hi₀ a).trans ha)]
      exact hmem a
    · exact IntermediateField.subset_adjoin _ _ (Or.inr hy)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]

omit [Module.Finite ℤ_[p] O] in

theorem finite_of_intEmb_eq {j : O →+* integralClosure ℤ_[p] L} (hj : ∀ a, intEmb L (j a) = i a) :
    j.Finite := by
  have h : j.comp (algebraMap ℤ_[p] O) = algebraMap ℤ_[p] (integralClosure ℤ_[p] L) :=
    RingHom.ext fun z => intEmb_injective L (by
      rw [RingHom.comp_apply, hj, map_algebraMap_padicInt i hi]
      exact (map_algebraMap_padicInt (intEmb L) (norm_intEmb_le_one L) z).symm)
  refine RingHom.Finite.of_comp_finite (f := algebraMap ℤ_[p] O) ?_
  rw [h, RingHom.finite_algebraMap]
  infer_instance

omit [Module.Finite ℤ_[p] O] in
theorem isLocalHom_of_intEmb_eq (hinj : Function.Injective i)
    {j : O →+* integralClosure ℤ_[p] L} (hj : ∀ a, intEmb L (j a) = i a) : IsLocalHom j :=
  RingHom.IsIntegral.isLocalHom (finite_of_intEmb_eq i hi L hj).to_isIntegral
    fun a b h => hinj (by rw [← hj, ← hj, h])

theorem norm_map_eq_one_iff (hinj : Function.Injective i) (x : O) : ‖i x‖ = 1 ↔ IsUnit x := by
  have := finiteDimensional_genField i hi Set.finite_empty
  obtain ⟨j, hj⟩ := exists_comp_eq_of_mem_range _ (intEmb_injective (genField i ∅)) i fun a =>
    (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi (Set.empty_subset _) a, hi a⟩
  have := isLocalHom_of_intEmb_eq i hi _ hinj hj
  rw [← hj, ← isUnit_iff_norm, isUnit_map_iff]

omit [Module.Finite ℤ_[p] O] [Algebra ℤ_[p] O] in

theorem exists_intEmb_eq_discEval (hiL : ∀ x, i x ∈ (fieldEmb L).fieldRange) {t : ℂ_[p]}
    (htL : t ∈ (fieldEmb L).fieldRange) (ht : ‖t‖ < 1) :
    ∃ ev : O⟦X⟧ →+* integralClosure ℤ_[p] L, ∀ f, intEmb L (ev f) = discEval i hi ht f :=
  exists_comp_eq_of_mem_range _ (intEmb_injective L) _ fun f =>
    (mem_range_intEmb_iff L _).2 ⟨discEval_mem i hi ht (B := (fieldEmb L).fieldRange.toSubring)
      (isClosed_fieldRange L) hiL htL f, norm_discEval_le_one i hi ht f⟩

omit [Module.Finite ℤ_[p] O] in

theorem isLocalHom_of_intEmb_eq_discEval (hinj : Function.Injective i) {t : ℂ_[p]} (ht : ‖t‖ < 1)
    {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} (hev : ∀ f, intEmb L (ev f) = discEval i hi ht f) :
    IsLocalHom ev := by
  have hj : ∀ a, intEmb L (ev.comp PowerSeries.C a) = i a := fun a => by simp [hev]
  have := isLocalHom_of_intEmb_eq i hi L hinj hj
  refine ⟨fun f hf => PowerSeries.isUnit_iff_constantCoeff.2 ?_⟩
  rw [← isUnit_map_iff (ev.comp PowerSeries.C), isUnit_iff_norm, hj]
  rw [isUnit_iff_norm, hev] at hf
  refine le_antisymm (hi _) (not_lt.1 fun h => hf.not_lt ?_)
  rw [← sub_add_cancel (discEval i hi ht f) (i (PowerSeries.constantCoeff f))]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    (max_lt ((norm_discEval_sub_le i hi ht f).trans_lt ht) h)

end Finite

theorem exists_injective_norm_le_one (O : Type*) [CommRing O] [IsDomain O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (hp : (p : O) ≠ 0) :
    ∃ i : O →+* ℂ_[p], Function.Injective i ∧ ∀ x, ‖i x‖ ≤ 1 := by
  obtain ⟨L, _, g, hg⟩ := exists_injective_algHom_integralClosure O hp
  exact ⟨(intEmb L).comp g, (intEmb_injective L).comp hg, fun x => norm_intEmb_le_one L _⟩

section Points

variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

def IsDiscPoint (L : IntermediateField ℚ_[p] (PadicAlgCl p)) {t : ℂ_[p]} (ht0 : t ≠ 0)
    (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L) : Prop :=
  (∀ f, intEmb L (ev f) = discEval i hi ht f) ∧
    ∀ f, fieldEmb L (evA f) = discEvalAway π A i hi hπ ht0 ht f

variable {i hi hπ A} in

theorem IsDiscPoint.comp_algebraMap {L : IntermediateField ℚ_[p] (PadicAlgCl p)} {t : ℂ_[p]}
    {ht0 : t ≠ 0} {ht : ‖t‖ < 1} {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} {evA : A →+* L}
    (h : IsDiscPoint i hi hπ A L ht0 ht ev evA) :
    evA.comp (algebraMap O⟦X⟧ A) = (algebraMap (integralClosure ℤ_[p] L) L).comp ev :=
  RingHom.ext fun f => (fieldEmb L).injective (by
    rw [RingHom.comp_apply, h.2, discEvalAway_algebraMap, ← h.1]
    rfl)

theorem exists_isDiscPoint (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
    (hiL : ∀ x, i x ∈ (fieldEmb L).fieldRange) {t : ℂ_[p]} (htL : t ∈ (fieldEmb L).fieldRange)
    (ht0 : t ≠ 0) (ht : ‖t‖ < 1) : ∃ ev evA, IsDiscPoint i hi hπ A L ht0 ht ev evA := by
  obtain ⟨ev, hev⟩ := exists_intEmb_eq_discEval i hi L hiL htL ht
  obtain ⟨evA, hevA⟩ := exists_comp_eq_of_mem_range _ (fieldEmb L).injective
    (discEvalAway π A i hi hπ ht0 ht)
    fun f => discEvalAway_mem i hi hπ ht0 ht (isClosed_fieldRange L) hiL htL f
  exact ⟨ev, evA, hev, hevA⟩

end Points

section Frames

open MvPolynomial

variable (p) in

def algInt : Subring ℂ_[p] where
  carrier := {x | x ∈ algField p ∧ ‖x‖ ≤ 1}
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by
    rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_mem _, norm_one.le⟩
  add_mem' ha hb := ⟨add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩

theorem isUnit_algInt_iff (x : algInt p) : IsUnit x ↔ ‖(x : ℂ_[p])‖ = 1 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_right_inv
    have h1 : ‖(x : ℂ_[p])‖ * ‖(y : ℂ_[p])‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, hy, Subring.coe_one, norm_one]
    exact le_antisymm x.2.2 (h1.ge.trans (mul_le_of_le_one_right (norm_nonneg _) y.2.2))
  · intro h
    have h0 : (x : ℂ_[p]) ≠ 0 := norm_pos_iff.1 (h ▸ one_pos)
    exact IsUnit.of_mul_eq_one ⟨(x : ℂ_[p])⁻¹, inv_mem x.2.1, by rw [norm_inv, h, inv_one]⟩
      (Subtype.ext (mul_inv_cancel₀ h0))

variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]

def BoundedOnFrames (F : MvPolynomial (EntryIndex n n) A) : Prop :=
  ∀ t ∈ algField p, ∀ (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (g : ∀ s, GL (n s) (algInt p)),
    ‖eval₂ (discEvalAway π A i hi hπ ht0 ht)
      (entries fun s => (g s : Matrix (n s) (n s) (algInt p)).map (algInt p).subtype) F‖ ≤ 1

def IntegralOnFrames (F : MvPolynomial (EntryIndex n n) A) : Prop :=
  ∀ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] (t : ℂ_[p])
    (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L),
    IsDiscPoint i hi hπ A L ht0 ht ev evA → ∀ g : ∀ s, GL (n s) (integralClosure ℤ_[p] L),
      eval₂ evA (entries fun s => (g s : Matrix (n s) (n s) (integralClosure ℤ_[p] L)).map
        (algebraMap (integralClosure ℤ_[p] L) L)) F ∈ integralClosure ℤ_[p] L

theorem boundedOnFrames_iff_integralOnFrames [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (F : MvPolynomial (EntryIndex n n) A) :
    BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F := by
  have key : ∀ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (t : ℂ_[p]) (ht0 : t ≠ 0)
      (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L),
      IsDiscPoint i hi hπ A L ht0 ht ev evA → ∀ y : EntryIndex n n → L,
        fieldEmb L (eval₂ evA y F) =
          eval₂ (discEvalAway π A i hi hπ ht0 ht) (fun k => fieldEmb L (y k)) F := by
    intro L t ht0 ht ev evA h y
    rw [eval₂_comp_left, show (fieldEmb L).comp evA = _ from RingHom.ext h.2]
    rfl
  constructor
  · intro hF L _ t ht0 ht ev evA h g
    let e : integralClosure ℤ_[p] L →+* algInt p := (intEmb L).codRestrict _ fun x =>
      ⟨fieldEmb_mem_algField L x, norm_intEmb_le_one L x⟩
    have htK : t ∈ algField p := by
      rw [← discEval_X i hi ht, ← h.1]
      exact fieldEmb_mem_algField L _
    rw [mem_integralClosure_iff_norm, key L t ht0 ht ev evA h]
    exact hF t htK ht0 ht fun s => Matrix.GeneralLinearGroup.map e (g s)
  · intro hF t htK ht0 ht g
    set x := entries fun s => (g s : Matrix (n s) (n s) (algInt p)).map (algInt p).subtype
    have hT : insert t (Set.range x) ⊆ algField p :=
      Set.insert_subset htK (by rintro _ ⟨k, rfl⟩; exact ((g k.1).1 k.2.1 k.2.2).2.1)
    have := finiteDimensional_genField i hi ((Set.finite_range x).insert t)
    set L := genField i (insert t (Set.range x))
    obtain ⟨ev, evA, h⟩ := exists_isDiscPoint i hi hπ A L (map_mem_genField i hi hT)
      (mem_genField_of_mem i hi hT (Set.mem_insert _ _)) ht0 ht
    choose y hy using fun k => (mem_range_intEmb_iff L (x k)).2
      ⟨mem_genField_of_mem i hi hT (Set.mem_insert_of_mem _ ⟨k, rfl⟩), ((g k.1).1 k.2.1 k.2.2).2.2⟩
    have hu : ∀ s, IsUnit (ofEntries y s) := fun s => by
      have h1 : (intEmb L).mapMatrix (ofEntries y s) =
          (algInt p).subtype.mapMatrix (g s : Matrix (n s) (n s) (algInt p)) := by
        ext a b
        exact hy ⟨s, a, b⟩
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_norm, RingHom.map_det, h1, ← RingHom.map_det]
      exact (isUnit_algInt_iff _).1 ((Matrix.isUnit_iff_isUnit_det _).1 (g s).isUnit)
    have h2 := hF L t ht0 ht ev evA h fun s => (hu s).unit
    rw [mem_integralClosure_iff_norm, key L t ht0 ht ev evA h] at h2
    have h3 : x = fun k => intEmb L (y k) := funext fun k => (hy k).symm
    rw [h3]
    exact h2

variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}

theorem BoundedOnFrames.coeffPoly_integral (hF : BoundedOnFrames i hi hπ F) (m : ℤ) :
    (∀ μ, ‖coeff μ (coeffPoly m (map (laurent π A i hπ) F))‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by
  refine coeffPoly_integral_of_admissible (algField p) (residueFieldInfiniteOn_algField p)
    (algDisc p) (fun _ ht => ht.2) (algDisc_dense p) (mul_mem_algDisc p) i hi hπ
    (detProdPoly ℂ_[p] n) (norm_coeff_detProdPoly_le n) (exists_norm_coeff_detProdPoly n) F
    (fun t htS ht0 ht x hx hxδ => ?_) m
  let y : EntryIndex n n → algInt p := fun k => ⟨x k, hx k⟩
  have h1 : IsUnit (∏ s, (ofEntries y s).det) := by
    rw [isUnit_algInt_iff, ← hxδ, eval_detProdPoly, ← Subring.coe_subtype, map_prod]
    simp only [RingHom.map_det]
    rfl
  rw [IsUnit.prod_univ_iff] at h1
  exact hF t htS.1 ht0 ht fun s => ((Matrix.isUnit_iff_isUnit_det _).2 (h1 s)).unit

theorem BoundedOnFrames.norm_coeff_bind₁_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {τ : Type*} {g : EntryIndex n n → MvPolynomial τ ℂ_[p]} {c : ℝ}
    (hc : 0 ≤ c) (hg : ∀ k μ, ‖coeff μ (g k)‖ ≤ c) (μ : τ →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => map HahnSeries.C (g k)) (map (laurent π A i hπ) F))).coeff m‖ ≤
        c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => map HahnSeries.C (g k))
        (map (laurent π A i hπ) F))).coeff m = 0) := by
  rw [← coeff_coeffPoly, coeffPoly_bind₁]
  exact ⟨DiscEval.norm_coeff_bind₁_le (isHomogeneous_coeffPoly m (hd.map _))
    (hF.coeffPoly_integral m).1 hc hg μ, fun hm => by simp [(hF.coeffPoly_integral m).2 hm]⟩

theorem BoundedOnFrames.norm_coeff_linear_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {B : EntryIndex n n → EntryIndex n n → ℂ_[p]} {c : ℝ}
    (hc : 1 ≤ c) (hB : ∀ k l, ‖B k l‖ ≤ c) (μ : EntryIndex n n →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F))).coeff m = 0) := by
  have h : (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l :
      EntryIndex n n → MvPolynomial (EntryIndex n n) ℂ_[p]⸨X⸩) =
      fun k => map HahnSeries.C (∑ l, C (B k l) * X l) := by
    funext k
    simp only [map_sum, map_mul, map_C, map_X]
  rw [h, ← coeff_coeffPoly, coeffPoly_bind₁]
  exact ⟨ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.basisChange_holds _ _ _ d (isHomogeneous_coeffPoly m (hd.map _))
    (hF.coeffPoly_integral m).1 B c hc hB μ, fun hm => by simp [(hF.coeffPoly_integral m).2 hm]⟩

theorem BoundedOnFrames.norm_coeff_mul_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {κ : ι → Type*} [∀ s, Fintype (κ s)]
    {w : ∀ s, Matrix (n s) (κ s) ℂ_[p]} {c : ℝ} (hc : 0 ≤ c) (hw : ∀ s a b, ‖w s a b‖ ≤ c)
    (μ : EntryIndex κ n →₀ ℕ) (m : ℤ) :
    ‖(coeff μ (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (coeff μ (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F))).coeff m = 0) := by
  classical
  have h : (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩ :
      EntryIndex n n → MvPolynomial (EntryIndex κ n) ℂ_[p]⸨X⸩) =
      fun k => map HahnSeries.C (∑ j, C (w k.1 k.2.1 j) * X ⟨k.1, j, k.2.2⟩) := by
    funext k
    simp only [map_sum, map_mul, map_C, map_X]
  rw [h]
  refine hF.norm_coeff_bind₁_le hd hc (fun k ν => ?_) μ m
  rw [coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun j _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp [hw, hc]

theorem boundedOnFrames_map (F₀ : MvPolynomial (EntryIndex n n) O⟦X⟧) :
    BoundedOnFrames i hi hπ (map (algebraMap O⟦X⟧ A) F₀) := by
  intro t _ ht0 ht g
  rw [eval₂_map, eval₂_eq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [norm_mul, RingHom.comp_apply, discEvalAway_algebraMap, norm_prod]
  refine mul_le_one₀ (norm_discEval_le_one i hi ht _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_)
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ((g k.1).1 k.2.1 k.2.2).2.2

end Frames

end Padic

open MvPolynomial in

theorem main (p : ℕ) [Fact p.Prime] :
    (ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (algField p : Set ℂ_[p]) ∧
      (∀ t ∈ algDisc p, 0 < ‖t‖ ∧ ‖t‖ < 1) ∧
      (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ algDisc p, |‖t‖ - r| < ε) ∧
      ∀ t ∈ algDisc p, ∀ τ ∈ algField p, ‖τ‖ = 1 → t * τ ∈ algDisc p) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] (i : O →+* ℂ_[p])
      (hi : ∀ x, ‖i x‖ ≤ 1) (_ : Function.Injective i) (π : O) (hπ : i π ≠ 0)
      (A : Type) [CommRing A] [Algebra O⟦X⟧ A]
      [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A],
      (∀ (t : ℂ_[p]) (ht0 : t ≠ 0) (ht : ‖t‖ < 1),
        (∀ f : O⟦X⟧,
          HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) ∧
          discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f) ∧
        (∀ T : Set ℂ_[p], T.Finite → T ⊆ algField p → t ∈ T →
          (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) ∧
          ∃ (_ : FiniteDimensional ℚ_[p] (genField i T))
            (_ : IsDiscreteValuationRing (integralClosure ℤ_[p] (genField i T))),
            IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] (genField i T)))
              (integralClosure ℤ_[p] (genField i T)) ∧
            Finite (ResidueField (integralClosure ℤ_[p] (genField i T))) ∧
            IsFractionRing (integralClosure ℤ_[p] (genField i T)) (genField i T) ∧
            ∃ (ev : O⟦X⟧ →+* integralClosure ℤ_[p] (genField i T)) (evA : A →+* genField i T),
              (∀ f, intEmb _ (ev f) = discEval i hi ht f) ∧
              (∀ f, fieldEmb _ (evA f) = discEvalAway π A i hi hπ ht0 ht f) ∧
              evA.comp (algebraMap O⟦X⟧ A) = (algebraMap _ (genField i T)).comp ev ∧
              IsLocalHom ev ∧ (ev.comp PowerSeries.C).Finite ∧
              IsLocalHom (ev.comp PowerSeries.C)) ∧
        (∀ f : A,
          Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) ∧
          HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
            (discEvalAway π A i hi hπ ht0 ht f)) ∧
        ∀ (f : A) (a b : ℕ) (f₀ : O⟦X⟧),
          f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ →
          discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ ∧
          ∀ n : ℤ, (laurent π A i hπ f).coeff n =
            if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀)) ∧
      ∀ (ι : Type) [Fintype ι] (n : ι → Type) [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
        (F : MvPolynomial (EntryIndex n n) A),
        (BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F) ∧
        ∀ d : ℕ, F.IsHomogeneous d → BoundedOnFrames i hi hπ F →
          ∀ (B : EntryIndex n n → EntryIndex n n → ℂ_[p]) (c : ℝ), 1 ≤ c → (∀ k l, ‖B k l‖ ≤ c) →
            ∀ (μ : EntryIndex n n →₀ ℕ) (m : ℤ),
              ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
              (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m = 0) := by
  refine ⟨⟨residueFieldInfiniteOn_algField p, fun _ ht => ht.2, algDisc_dense p, mul_mem_algDisc p⟩,
    fun O _ _ _ i hi hinj π hπ A _ _ _ => ⟨fun t ht0 ht => ⟨fun f =>
      ⟨hasSum_discEval i hi ht f, discEvalAway_algebraMap π A i hi hπ ht0 ht f⟩,
      fun T hT hTK htT => ⟨fieldRange_genField i hi hTK, ?_⟩,
      fun f => ⟨tendsto_norm_laurent_term i hi hπ ht0 ht f, hasSum_laurent i hi hπ ht0 ht f⟩,
      fun f a b f₀ h => ⟨discEvalAway_eq i hi hπ ht0 ht h, coeff_laurent i hπ h⟩⟩,
    fun ι _ n _ _ F => ⟨boundedOnFrames_iff_integralOnFrames i hi hπ F,
      fun d hd hF B c hc hB μ m => hF.norm_coeff_linear_le hd hc hB μ m⟩⟩⟩
  have := finiteDimensional_genField i hi hT
  obtain ⟨ev, evA, h⟩ := exists_isDiscPoint i hi hπ A (genField i T) (map_mem_genField i hi hTK)
    (mem_genField_of_mem i hi hTK htT) ht0 ht
  have hj : ∀ a, intEmb _ (ev.comp PowerSeries.C a) = i a := fun a => by simp [h.1]
  exact ⟨this, inferInstance, isAdicComplete_integralClosure _,
    finite_residueField_integralClosure _, inferInstance, ev, evA, h.1, h.2, h.comp_algebraMap,
    isLocalHom_of_intEmb_eq_discEval i hi _ hinj ht h.1, finite_of_intEmb_eq i hi _ hj,
    isLocalHom_of_intEmb_eq i hi _ hinj hj⟩

example (p : ℕ) [Fact p.Prime] :
    ∃ (i : ℤ_[p] →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) (_ : Function.Injective i) (hπ : i p ≠ 0),
      ‖i p‖ < 1 ∧ BoundedOnFrames i hi hπ (MvPolynomial.map (algebraMap ℤ_[p]⟦X⟧
        (Localization.Away (PowerSeries.C (p : ℤ_[p]) * PowerSeries.X : ℤ_[p]⟦X⟧)))
        (detProdPoly ℤ_[p]⟦X⟧ fun _ : Fin 2 => Fin 3)) := by
  have hp : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  obtain ⟨i, hinj, hi⟩ := exists_injective_norm_le_one (p := p) ℤ_[p] hp.ne_zero
  exact ⟨i, hi, hinj, (map_ne_zero_iff i hinj).2 hp.ne_zero,
    (hi p).lt_of_ne fun h => hp.not_isUnit ((norm_map_eq_one_iff i hi hinj p).1 h),
    boundedOnFrames_map _⟩

end GlobalTheory.DiscEval

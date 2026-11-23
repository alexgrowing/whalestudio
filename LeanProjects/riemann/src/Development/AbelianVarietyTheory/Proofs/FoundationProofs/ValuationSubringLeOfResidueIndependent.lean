import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.BertiniNoether

theorem aeval_mem_valuationSubring {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] {t : L}
    {V : ValuationSubring F} {W : ValuationSubring L} (h : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (P : Polynomial F) (hP : ∀ i, P.coeff i ∈ V) : Polynomial.aeval t P ∈ W := by
  rw [Polynomial.aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem ((h _).2 (hP i)) (pow_mem ht i)

theorem eval₂_mem_valuationSubring {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] {t ω : L}
    {V : ValuationSubring F} {W : ValuationSubring L} (h : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (hω : ω ∈ W) (R : Polynomial (Polynomial F)) (hR : ∀ i j, (R.coeff i).coeff j ∈ V) :
    R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (aeval_mem_valuationSubring h ht _ (hR i)) (pow_mem hω i)

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma mem_of_gauss_valuation_eq_one {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L)
    (hG : ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
      (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1) :
    t ∈ W := by
  have h := hG X (fun i => by
      rw [coeff_X]; split_ifs
      · exact V.one_mem
      · exact V.zero_mem)
    ⟨1, by simp, by simpa using V.one_mem, by simpa using V.one_mem⟩
  rw [aeval_X] at h
  rw [← W.valuation_le_one_iff, h]

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma mem_of_monic_root_coeff_mem {L : Type} [Field L] (W : ValuationSubring L) (ψ : L[X])
    (hψ : ψ.Monic) (hc : ∀ i, ψ.coeff i ∈ W) (ω : L) (hω : ψ.eval ω = 0) : ω ∈ W := by
  have hl : ψ ∈ lifts (algebraMap W L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hψ
  have hint : IsIntegral W ω := ⟨q, hqm, by rw [← eval_map, hq, hω]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma aeval_mem_of_coeff_mem {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L) (hF : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (P : F[X]) (hP : ∀ i, P.coeff i ∈ V) : aeval t P ∈ W := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem ((hF _).2 (hP i)) (pow_mem ht i)

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma mem_of_monic_bipoly_root {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L) (hF : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (Φ : Polynomial (Polynomial F)) (ω : L) (hΦ : Φ.Monic)
    (hΦV : ∀ i j, (Φ.coeff i).coeff j ∈ V) (hΦω : Φ.eval₂ (aeval t).toRingHom ω = 0) : ω ∈ W :=
  mem_of_monic_root_coeff_mem W (Φ.map (aeval t).toRingHom) (hΦ.map _)
    (fun i => by rw [coeff_map]; exact aeval_mem_of_coeff_mem t V W hF ht _ (hΦV i)) ω
    (by rw [eval_map, hΦω])

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma exists_mul_mem_finset_and_eq_one {F : Type} [Field F] (V : ValuationSubring F) (s : Finset F)
    (hs : ∃ a ∈ s, a ≠ 0) : ∃ c : F, c ≠ 0 ∧ (∀ a ∈ s, c * a ∈ V) ∧ ∃ a ∈ s, c * a = 1 := by
  obtain ⟨a, ha, ha0⟩ := hs
  obtain ⟨b, hb, hmax⟩ := s.exists_max_image V.valuation ⟨a, ha⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    have := hmax a ha
    rw [hb0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ha0 this
  refine ⟨b⁻¹, inv_ne_zero hb0, fun x hx => ?_, b, hb, inv_mul_cancel₀ hb0⟩
  rw [← V.valuation_le_one_iff, map_mul, map_inv₀]
  have hvb : V.valuation b ≠ 0 := (Valuation.ne_zero_iff _).2 hb0
  rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvb), mul_one]
  exact hmax x hx

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma exists_mul_coeff_mem_and_eq_one {F : Type} [Field F] (V : ValuationSubring F) (P : F[X])
    (hP : P ≠ 0) : ∃ c : F, c ≠ 0 ∧ (∀ i, c * P.coeff i ∈ V) ∧ ∃ i, c * P.coeff i = 1 := by
  classical
  obtain ⟨c, hc0, hcV, a, ha, hca⟩ := exists_mul_mem_finset_and_eq_one V (P.support.image P.coeff) (by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.2 hP
    exact ⟨_, Finset.mem_image_of_mem _ hi, Polynomial.mem_support_iff.1 hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
  refine ⟨c, hc0, fun j => ?_, i, hca⟩
  by_cases hj : P.coeff j = 0
  · rw [hj, mul_zero]; exact V.zero_mem
  · exact hcV _ (Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.2 hj))

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma exists_mul_coeff_coeff_mem_and_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    (P : Polynomial (Polynomial F)) (hP : P ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ (∀ i j, c * (P.coeff i).coeff j ∈ V) ∧ ∃ i j, c * (P.coeff i).coeff j = 1 := by
  classical
  obtain ⟨c, hc0, hcV, a, ha, hca⟩ := exists_mul_mem_finset_and_eq_one V
    (P.support.biUnion fun i => (P.coeff i).support.image (P.coeff i).coeff) (by
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.2 hP
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 (Polynomial.mem_support_iff.1 hi)
      exact ⟨_, Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image_of_mem _ hj⟩,
        Polynomial.mem_support_iff.1 hj⟩)
  obtain ⟨i, -, ha⟩ := Finset.mem_biUnion.1 ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
  refine ⟨c, hc0, fun k l => ?_, i, j, hca⟩
  by_cases hkl : (P.coeff k).coeff l = 0
  · rw [hkl, mul_zero]; exact V.zero_mem
  · have hk : P.coeff k ≠ 0 := fun h => hkl (by rw [h, Polynomial.coeff_zero])
    exact hcV _ (Finset.mem_biUnion.2 ⟨k, Polynomial.mem_support_iff.2 hk,
      Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.2 hkl)⟩)

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
private lemma eval₂_aeval_mem_of_coeff_coeff_mem {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L) (hF : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (ω : L) (hω : ω ∈ W) (P : Polynomial (Polynomial F))
    (hP : ∀ i j, (P.coeff i).coeff j ∈ V) : P.eval₂ (aeval t).toRingHom ω ∈ W := by
  rw [eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (aeval_mem_of_coeff_mem t V W hF ht _ (hP i)) (pow_mem hω i)

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in
theorem _root_.GlobalTheory.BertiniNoether.le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  intro F _ L _ _ t V Φ ω hΦ hΦV hΦω hrep W₁ W₂ ⟨h₁F, h₁G⟩ ⟨h₂F, h₂G⟩ hmin y hy
  obtain ⟨Q, hQ0, R, hQR⟩ := hrep y
  have ht₂ : t ∈ W₂ := mem_of_gauss_valuation_eq_one t V W₂ h₂G
  have hω₂ : ω ∈ W₂ := mem_of_monic_bipoly_root t V W₂ h₂F ht₂ Φ ω hΦ hΦV hΦω
  have hΦ1 : Φ ≠ 1 := by
    rintro rfl
    simp at hΦω

  obtain ⟨d, hd0, hdV, i₀, hdi₀⟩ := exists_mul_coeff_mem_and_eq_one V Q hQ0
  set Q' : F[X] := C d * Q with hQ'
  have hQ'V : ∀ i, Q'.coeff i ∈ V := fun i => by rw [hQ', coeff_C_mul]; exact hdV i
  have hQ'prim : ∃ i, Q'.coeff i ≠ 0 ∧ Q'.coeff i ∈ V ∧ (Q'.coeff i)⁻¹ ∈ V :=
    ⟨i₀, by rw [hQ', coeff_C_mul, hdi₀]; exact one_ne_zero,
      by rw [hQ', coeff_C_mul, hdi₀]; exact V.one_mem,
      by rw [hQ', coeff_C_mul, hdi₀, inv_one]; exact V.one_mem⟩
  have hv₁Q := h₁G Q' hQ'V hQ'prim
  have hv₂Q := h₂G Q' hQ'V hQ'prim
  have hQ'eval : aeval t Q' = algebraMap F L d * aeval t Q := by
    rw [hQ', map_mul, aeval_C]

  set R₀ := R %ₘ Φ with hR₀def
  have hR₀ : R₀.eval₂ (aeval t).toRingHom ω = R.eval₂ (aeval t).toRingHom ω := by
    conv_rhs => rw [← modByMonic_add_div R Φ]
    rw [eval₂_add, eval₂_mul, hΦω, zero_mul, add_zero]
  have hdeg : R₀.natDegree < Φ.natDegree := natDegree_modByMonic_lt R hΦ hΦ1
  by_cases hR0 : R₀ = 0
  · have hy0 : y = 0 := by
      have hQne : aeval t Q' ≠ 0 := by
        intro h
        rw [h, map_zero] at hv₁Q
        exact zero_ne_one hv₁Q
      have : aeval t Q' * y = 0 := by
        rw [hQ'eval, mul_assoc, hQR, ← hR₀, hR0, eval₂_zero, mul_zero]
      exact (mul_eq_zero.1 this).resolve_left hQne
    rw [hy0]
    exact W₂.zero_mem
  obtain ⟨c, hc0, hcV, i₁, j₁, hci₁⟩ := exists_mul_coeff_coeff_mem_and_eq_one V R₀ hR0
  set R' : Polynomial (Polynomial F) := C (C c) * R₀ with hR'
  have hR'coeff : ∀ i j, (R'.coeff i).coeff j = c * (R₀.coeff i).coeff j := fun i j => by
    rw [hR', coeff_C_mul, coeff_C_mul]
  have hR'V : ∀ i j, (R'.coeff i).coeff j ∈ V := fun i j => by rw [hR'coeff]; exact hcV i j
  have hR'deg : R'.natDegree < Φ.natDegree := lt_of_le_of_lt (natDegree_C_mul_le _ _) hdeg
  have hR'unit : ¬ R'.eval₂ (aeval t).toRingHom ω ∈ W₁.nonunits := by
    intro h
    have := V.mem_nonunits_iff.1 (hmin R' hR'deg hR'V h i₁ j₁)
    rw [hR'coeff, hci₁, map_one] at this
    exact lt_irrefl _ this
  have hR'eval : R'.eval₂ (aeval t).toRingHom ω = algebraMap F L c * R₀.eval₂ (aeval t).toRingHom ω := by
    rw [hR', eval₂_mul, eval₂_C]
    simp

  set u : F := d * c⁻¹ with hu
  have hrel : aeval t Q' * y = algebraMap F L u * R'.eval₂ (aeval t).toRingHom ω := by
    rw [hQ'eval, mul_assoc, hQR, ← hR₀, hR'eval, hu, map_mul, map_inv₀]
    have : algebraMap F L c ≠ 0 := (_root_.map_ne_zero _).2 hc0
    field_simp
  have hval : ∀ W : ValuationSubring L, W.valuation (aeval t Q') = 1 →
      W.valuation y = W.valuation (algebraMap F L u) * W.valuation (R'.eval₂ (aeval t).toRingHom ω) := by
    intro W hW
    have := congrArg W.valuation hrel
    rwa [Valuation.map_mul, Valuation.map_mul, hW, one_mul] at this
  have hu₁ : algebraMap F L u ∈ W₁ := by
    rw [← W₁.valuation_le_one_iff]
    have h1 : 1 ≤ W₁.valuation (R'.eval₂ (aeval t).toRingHom ω) := by
      rw [W₁.mem_nonunits_iff, not_lt] at hR'unit
      exact hR'unit
    calc W₁.valuation (algebraMap F L u)
        ≤ W₁.valuation (algebraMap F L u) * W₁.valuation (R'.eval₂ (aeval t).toRingHom ω) :=
          le_mul_of_one_le_right' h1
      _ = W₁.valuation y := (hval W₁ hv₁Q).symm
      _ ≤ 1 := (W₁.valuation_le_one_iff y).2 hy
  have hu₂ : algebraMap F L u ∈ W₂ := (h₂F u).2 ((h₁F u).1 hu₁)
  have hR'₂ : R'.eval₂ (aeval t).toRingHom ω ∈ W₂ := eval₂_aeval_mem_of_coeff_coeff_mem t V W₂ h₂F ht₂ ω hω₂ R' hR'V
  rw [← W₂.valuation_le_one_iff, hval W₂ hv₂Q]
  exact mul_le_one' ((W₂.valuation_le_one_iff _).2 hu₂) ((W₂.valuation_le_one_iff _).2 hR'₂)

end GlobalTheory.BertiniNoether

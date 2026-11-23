import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSubSqLtOneOfTwoLtOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRootStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitMulSqQuadraticDefectStepStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

namespace Defect

variable {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)

theorem exists_exp {x : K} (hx : x ≠ 0) : ∃ n : ℤ, w x = WithZero.exp n :=
  ⟨WithZero.log (w x), (WithZero.exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩

theorem map_two_le : w 2 ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact w.map_add_le (by simp) (by simp)

theorem map_four_le : w 4 ≤ 1 := by
  have : (4 : K) = 2 + 2 := by norm_num
  rw [this]
  exact w.map_add_le (map_two_le w) (map_two_le w)

theorem evenNorms_of_le_four (h2 : (2 : K) ≠ 0)
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x) (δ : K) (hδ : w δ = 1) (hns : ¬ IsSquare δ)
    (h : w (δ - 1) ≤ w 4) : EvenNorms w δ := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hw4 : 0 < w 4 := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 h4)
  set ρ : K := (δ - 1) / 4 with hρ
  have hδρ : δ = 1 + 4 * ρ := by rw [hρ]; field_simp; ring
  have hρ1 : w ρ ≤ 1 := by rw [hρ, map_div₀]; exact div_le_one_of_le₀ h zero_le'
  rw [hδρ]
  refine GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root K w ρ h2 hρ1 fun x hx => ?_
  have hle : w (x ^ 2 + x - ρ) ≤ 1 := by
    refine w.map_sub_le (w.map_add_le ?_ hx) hρ1
    rw [map_pow]; exact pow_le_one₀ zero_le' hx
  refine le_antisymm hle (not_lt.1 fun hlt => hns ?_)
  have e1 : δ - (1 + 2 * x) ^ 2 = -(4 * (x ^ 2 + x - ρ)) := by rw [hδρ]; ring
  have l1 : w (δ - (1 + 2 * x) ^ 2) < w 4 := by
    rw [e1, Valuation.map_neg, map_mul]
    exact mul_lt_of_lt_one_right hw4 hlt
  have l2 : w ((1 + 2 * x) ^ 2) = 1 := by
    rw [← hδ]
    refine w.map_eq_of_sub_lt ?_
    rw [Valuation.map_sub_swap, hδ]
    exact l1.trans_le (map_four_le w)
  have hy : (1 + 2 * x) ^ 2 ≠ 0 := by
    intro h0; rw [h0] at l2; simp at l2
  have hs : IsSquare (δ / (1 + 2 * x) ^ 2) := by
    refine hsq _ ?_
    rw [div_sub_one hy, map_div₀, l2, div_one]; exact l1
  have : δ = δ / (1 + 2 * x) ^ 2 * (1 + 2 * x) ^ 2 := (div_mul_cancel₀ _ hy).symm
  rw [this]
  exact hs.mul (IsSquare.sq _)

theorem not_isSquare_mul_sq {δ c : K} (hc : c ≠ 0) (hns : ¬ IsSquare δ) :
    ¬ IsSquare (δ * c ^ 2) := by
  intro h
  apply hns
  have : δ = δ * c ^ 2 * (c⁻¹) ^ 2 := by field_simp
  rw [this]
  exact h.mul (IsSquare.sq _)

theorem unit_case (h2 : (2 : K) ≠ 0) (π : K) (hπ : w π = WithZero.exp (-1))
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x)
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    (m : ℤ) (hm : w 4 = WithZero.exp m) (N : ℕ) :
    ∀ δ : K, w δ = 1 → ¬ IsSquare δ → w (δ - 1) ≤ WithZero.exp (m + N) →
      ∃ c : K, c ≠ 0 ∧ ((w (δ * c ^ 2) = 1 ∧ w 4 < w (δ * c ^ 2 - 1) ∧
        ∃ n : ℤ, w (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ EvenNorms w (δ * c ^ 2)) := by
  induction N with
  | zero =>
    intro δ hδ hns h
    refine ⟨1, one_ne_zero, Or.inr ?_⟩
    rw [one_pow, mul_one]
    exact evenNorms_of_le_four w h2 hsq δ hδ hns (by simpa [hm] using h)
  | succ N ih =>
    intro δ hδ hns h
    by_cases h4 : w (δ - 1) ≤ w 4
    · refine ⟨1, one_ne_zero, Or.inr ?_⟩
      rw [one_pow, mul_one]
      exact evenNorms_of_le_four w h2 hsq δ hδ hns h4
    rw [not_le] at h4
    have hne : δ - 1 ≠ 0 := by
      intro h0; rw [h0] at h4; simp at h4
    obtain ⟨d, hd⟩ := exists_exp w hne
    have hle : w (δ - 1) ≤ 1 := w.map_sub_le hδ.le (by simp)
    have hd0 : d ≤ 0 := by
      rw [hd, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle; exact hle
    rcases Int.even_or_odd' d with ⟨k, hk | hk⟩
    · have hw2 : w 2 < 1 := by
        refine lt_of_le_of_ne (map_two_le w) fun h1 => ?_
        have : w 4 = 1 := by
          have : (4 : K) = 2 * 2 := by norm_num
          rw [this, map_mul, h1, one_mul]
        rw [this] at h4
        exact absurd hle (not_le.2 h4)
      obtain ⟨c, hc, hlt⟩ := GlobalTheory.T.exists_unit_mul_sq_quadratic_defect_step K w δ π (-k).toNat hπ (hres hw2) hδ h4 (by
        rw [hd]; congr 1; omega)
      have hc0 : c ≠ 0 := by
        intro h0; rw [h0] at hc; simp at hc
      have hb : w (δ * c ^ 2 - 1) ≤ WithZero.exp (m + N) := by
        by_cases h0 : δ * c ^ 2 - 1 = 0
        · rw [h0]; simp
        obtain ⟨e, he⟩ := exists_exp w h0
        have := hlt.trans_le h
        rw [he, WithZero.exp_lt_exp] at this
        rw [he, WithZero.exp_le_exp]
        push_cast at this
        omega
      obtain ⟨c', hc', H⟩ := ih (δ * c ^ 2) (by simp [hδ, hc]) (not_isSquare_mul_sq hc0 hns) hb
      refine ⟨c * c', mul_ne_zero hc0 hc', ?_⟩
      have : δ * (c * c') ^ 2 = δ * c ^ 2 * c' ^ 2 := by ring
      rw [this]; exact H
    · refine ⟨1, one_ne_zero, Or.inl ?_⟩
      rw [one_pow, mul_one]
      exact ⟨hδ, h4, k, by rw [hd, hk]⟩

theorem general (h2 : (2 : K) ≠ 0) (π : K) (hπ : w π = WithZero.exp (-1))
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x)
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    (δ : K) (hδ : δ ≠ 0) (hns : ¬ IsSquare δ) :
    ∃ c : K, c ≠ 0 ∧ ((∃ n : ℤ, w (δ * c ^ 2) = WithZero.exp (2 * n + 1)) ∨
      (w (δ * c ^ 2) = 1 ∧ w 4 < w (δ * c ^ 2 - 1) ∧
        ∃ n : ℤ, w (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ EvenNorms w (δ * c ^ 2)) := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨m, hm⟩ := exists_exp w h4
  obtain ⟨d, hd⟩ := exists_exp w hδ
  rcases Int.even_or_odd' d with ⟨k, hk | hk⟩
  · have hπ0 : π ≠ 0 := by
      intro h0; rw [h0] at hπ; simp at hπ; exact WithZero.exp_ne_zero hπ.symm
    have hc0 : π ^ k ≠ 0 := zpow_ne_zero _ hπ0
    have hu : w (δ * (π ^ k) ^ 2) = 1 := by
      rw [map_mul, map_pow, map_zpow₀, hπ, hd, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
        ← WithZero.exp_add, ← WithZero.exp_zero]
      congr 1
      simp [hk]
    obtain ⟨c', hc', H⟩ := unit_case w h2 π hπ hsq hres m hm (-m).toNat _ hu
      (not_isSquare_mul_sq hc0 hns) (by
        refine (w.map_sub_le hu.le (by simp)).trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega)
    refine ⟨π ^ k * c', mul_ne_zero hc0 hc', Or.inr ?_⟩
    have : δ * (π ^ k * c') ^ 2 = δ * (π ^ k) ^ 2 * c' ^ 2 := by ring
    rw [this]; exact H
  · refine ⟨1, one_ne_zero, Or.inl ⟨k, ?_⟩⟩
    rw [one_pow, mul_one, hd, hk]

end Defect

open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem evenNorms_of_valuation_sub_one_le_four (F : Type) [Field F]
    [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : v.adicCompletion F)
    (he : Valued.v e = 1) (hns : ¬ IsSquare e)
    (hle : Valued.v (e - 1) ≤ Valued.v (4 : v.adicCompletion F)) :
    _root_.GlobalTheory.QNorm.EvenNorms Valued.v e := by
  have h4 : (4 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 4]
    exact (map_ne_zero _).mpr (by norm_num)
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact (map_ne_zero _).mpr (by norm_num)
  have hw4 : 0 < Valued.v (4 : v.adicCompletion F) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h4)
  have hw4le : Valued.v (4 : v.adicCompletion F) ≤ 1 := by
    rw [show (4 : v.adicCompletion F) = 1 + 1 + 1 + 1 by norm_num]
    exact Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _
      (Valuation.map_one _).le (Valuation.map_one _).le) (Valuation.map_one _).le) (Valuation.map_one _).le
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : v.adicCompletion F, ρ = (e - 1) / 4 := ⟨_, rfl⟩
  have heρ : e = 1 + 4 * ρ := by rw [hρ_def]; field_simp; ring
  have hρ : Valued.v ρ ≤ 1 := by
    rw [hρ_def, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  rw [heρ]
  refine _root_.GlobalTheory.QNorm.evenNorms_one_add_four_mul _ Valued.v ρ h2 hρ ?_
  intro x hx
  have hint : Valued.v (x ^ 2 + x - ρ) ≤ 1 :=
    Valuation.map_sub_le _ (Valuation.map_add_le _ (by rw [map_pow]; exact pow_le_one₀ zero_le' hx) hx) hρ
  refine le_antisymm hint ?_
  by_contra hlt
  push_neg at hlt
  apply hns
  obtain ⟨s, hs_def⟩ : ∃ s : v.adicCompletion F, s = 1 + 2 * x := ⟨_, rfl⟩
  have hdiff : e - s ^ 2 = -(4 * (x ^ 2 + x - ρ)) := by rw [heρ, hs_def]; ring
  have hdiff_lt : Valued.v (e - s ^ 2) < Valued.v (4 : v.adicCompletion F) := by
    rw [hdiff, Valuation.map_neg, map_mul]
    exact mul_lt_of_lt_one_right hw4 hlt
  have hs2 : Valued.v (s ^ 2) = 1 := by
    rw [show s ^ 2 = e - (e - s ^ 2) by ring,
      Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact lt_of_lt_of_le hdiff_lt hw4le), he]
  have hs : Valued.v s = 1 := by rw [map_pow] at hs2; exact sq_eq_one.mp hs2
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v (e * s⁻¹ ^ 2) (by
    rw [show e * s⁻¹ ^ 2 - 1 = (e - s ^ 2) * s⁻¹ ^ 2 by field_simp, map_mul, map_pow, map_inv₀,
      hs, inv_one, one_pow, mul_one]
    exact hdiff_lt)
  refine ⟨r * s, ?_⟩
  have : e = (e * s⁻¹ ^ 2) * s ^ 2 := by field_simp
  rw [this, hr]; ring

open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem exists_normalForm_nonsquare_unit_lemma (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (π : v.adicCompletion F) (hπ : Valued.v π = WithZero.exp (-1))
    (hsq : Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1)
    (a : ℤ) (ha : Valued.v (4 : v.adicCompletion F) = WithZero.exp a) (n : ℕ) :
    ∀ e : v.adicCompletion F, Valued.v e = 1 → ¬ IsSquare e → ∀ j : ℤ,
      Valued.v (e - 1) = WithZero.exp j → j ≤ a + n →
      ∃ c : v.adicCompletion F, c ≠ 0 ∧ ((Valued.v (e * c ^ 2) = 1 ∧
        Valued.v (4 : v.adicCompletion F) < Valued.v (e * c ^ 2 - 1) ∧
        ∃ m : ℤ, Valued.v (e * c ^ 2 - 1) = WithZero.exp (2 * m + 1)) ∨
        _root_.GlobalTheory.QNorm.EvenNorms Valued.v (e * c ^ 2)) := by
  induction n with
  | zero =>
    intro e he hns j hj hja
    refine ⟨1, one_ne_zero, Or.inr ?_⟩
    rw [one_pow, mul_one]
    refine evenNorms_of_valuation_sub_one_le_four F v e he hns ?_
    rw [hj, ha, WithZero.exp_le_exp]
    simpa using hja
  | succ n ih =>
    intro e he hns j hj hja
    by_cases hle : j ≤ a + n
    · exact ih e he hns j hj hle
    have h4lt : Valued.v (4 : v.adicCompletion F) < Valued.v (e - 1) := by
      rw [ha, hj, WithZero.exp_lt_exp]; omega
    have he1 : Valued.v (e - 1) ≤ 1 :=
      Valuation.map_sub_le _ he.le (Valuation.map_one _).le
    rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨m, hm⟩
    · have hj0 : j ≤ 0 := by
        rw [hj, ← WithZero.exp_zero, WithZero.exp_le_exp] at he1; exact he1
      have h2 : Valued.v (2 : v.adicCompletion F) < 1 := by
        by_contra hge
        push_neg at hge
        have : 1 ≤ Valued.v (4 : v.adicCompletion F) := by
          rw [show (4 : v.adicCompletion F) = 2 ^ 2 by norm_num, map_pow]
          exact one_le_pow₀ hge
        exact absurd (lt_of_lt_of_le h4lt he1) (not_lt.mpr this)
      obtain ⟨c, hc, hlt⟩ := _root_.GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt _ Valued.v e π (-i).toNat hπ
        (hsq h2) he h4lt (by rw [hj]; congr 1; omega)
      have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      have he' : Valued.v (e * c ^ 2) = 1 := by rw [map_mul, map_pow, he, hc, one_pow, mul_one]
      have hns' : ¬ IsSquare (e * c ^ 2) := by
        rintro ⟨r, hr⟩
        apply hns
        refine ⟨r / c, ?_⟩
        have : e = (e * c ^ 2) / c ^ 2 := by field_simp
        rw [this, hr]; ring
      have hne : e * c ^ 2 - 1 ≠ 0 := by
        intro h
        apply hns'
        exact ⟨1, by rw [sub_eq_zero] at h; rw [h, mul_one]⟩
      have hv0 : Valued.v (e * c ^ 2 - 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
      obtain ⟨j', hj'⟩ : ∃ j' : ℤ, Valued.v (e * c ^ 2 - 1) = WithZero.exp j' :=
        ⟨WithZero.log _, (WithZero.exp_log hv0).symm⟩
      have hj'lt : j' < j := by rw [hj', hj, WithZero.exp_lt_exp] at hlt; exact hlt
      obtain ⟨c', hc'0, hc'⟩ := ih (e * c ^ 2) he' hns' j' hj' (by push_cast at hja; omega)
      refine ⟨c * c', mul_ne_zero hc0 hc'0, ?_⟩
      rw [show e * (c * c') ^ 2 = e * c ^ 2 * c' ^ 2 by ring]
      exact hc'
    · refine ⟨1, one_ne_zero, Or.inl ⟨by rw [one_pow, mul_one, he], by rwa [one_pow, mul_one],
        m, by rw [one_pow, mul_one, hj, hm]⟩⟩

open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem exists_sq_near_of_valuation_two_lt_one {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
    (R : Finset K) (hR : ∀ r ∈ R, w r ≤ 1) (hcov : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1)
    (h2 : w 2 < 1) (x : K) (hx : w x ≤ 1) : ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1 := by
  let S : Setoid {a : K // w a ≤ 1} :=
    { r := fun a b => w (a.1 - b.1) < 1
      iseqv :=
        { refl := fun a => by simp
          symm := fun {a b} h => by rwa [← Valuation.map_neg, neg_sub]
          trans := fun {a b c} hab hbc => by
            have : a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by ring
            rw [this]; exact Valuation.map_add_lt w hab hbc } }
  let sq : {a : K // w a ≤ 1} → {a : K // w a ≤ 1} :=
    fun a => ⟨a.1 ^ 2, by rw [map_pow]; exact pow_le_one₀ zero_le' a.2⟩
  have hsq : ∀ a b, S.r a b → S.r (sq a) (sq b) := by
    intro a b hab
    show w (a.1 ^ 2 - b.1 ^ 2) < 1
    rw [show a.1 ^ 2 - b.1 ^ 2 = (a.1 - b.1) * (a.1 + b.1) by ring, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le' (Valuation.map_add_le w a.2 b.2)) hab
  let g : Quotient S → Quotient S := Quotient.map sq hsq
  have hfin : Finite (Quotient S) := by
    refine Finite.of_surjective (fun r : R => Quotient.mk S ⟨r.1, hR r.1 r.2⟩) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      obtain ⟨r, hr, har⟩ := hcov a.1 a.2
      exact ⟨⟨r, hr⟩, Quotient.sound (by
        show w (r - a.1) < 1
        rwa [← Valuation.map_neg, neg_sub])⟩
  have hinj : Function.Injective g := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    have hab : w (a.1 ^ 2 - b.1 ^ 2) < 1 := Quotient.exact hpq
    apply Quotient.sound
    show w (a.1 - b.1) < 1
    have hsq2 : w ((a.1 - b.1) ^ 2) < 1 := by
      rw [show (a.1 - b.1) ^ 2 = (a.1 ^ 2 - b.1 ^ 2) + -(2 * b.1 * (a.1 - b.1)) by ring]
      refine Valuation.map_add_lt w hab ?_
      rw [Valuation.map_neg, map_mul, map_mul]
      refine lt_of_le_of_lt ?_ h2
      rw [mul_assoc]
      exact mul_le_of_le_one_right zero_le'
        (mul_le_one' b.2 (Valuation.map_sub_le w a.2 b.2))
    by_contra hge
    push_neg at hge
    rw [map_pow] at hsq2
    exact absurd hsq2 (not_lt.mpr (one_le_pow₀ hge))
  have hsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hinj
  obtain ⟨q, hq⟩ := hsurj (Quotient.mk S ⟨x, hx⟩)
  induction q using Quotient.inductionOn with
  | h y =>
  have hyx : w (y.1 ^ 2 - x) < 1 := Quotient.exact hq
  exact ⟨y.1, y.2, by rwa [← Valuation.map_neg, neg_sub]⟩

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.exists_normal_form_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ → ∃ c : v.adicCompletion F, c ≠ 0 ∧ ((∃ n : ℤ, Valued.v (δ * c ^ 2) = WithZero.exp (2 * n + 1)) ∨ (Valued.v (δ * c ^ 2) = 1 ∧ Valued.v (4 : v.adicCompletion F) < Valued.v (δ * c ^ 2 - 1) ∧ ∃ n : ℤ, Valued.v (δ * c ^ 2 - 1) = WithZero.exp (2 * n + 1)) ∨ _root_.GlobalTheory.QNorm.EvenNorms Valued.v (δ * c ^ 2)) := by
  intro F _ _ v δ hδ0 hδsq
  obtain ⟨⟨π₀, -, hπ⟩, -, -, R, -, hR, hcov⟩ := _root_.GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
  obtain ⟨π, hπ_def⟩ : ∃ π : v.adicCompletion F, π = algebraMap F (v.adicCompletion F) π₀ :=
    ⟨_, rfl⟩
  rw [← hπ_def] at hπ
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  have hvδ : Valued.v δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hδ0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v δ = WithZero.exp m := ⟨_, (WithZero.exp_log hvδ).symm⟩
  rcases Int.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · obtain ⟨c₀, hc₀_def⟩ : ∃ c₀ : v.adicCompletion F, c₀ = π ^ n := ⟨_, rfl⟩
    have hc₀0 : c₀ ≠ 0 := by rw [hc₀_def]; exact zpow_ne_zero _ hπ0
    have hvc₀ : Valued.v c₀ = WithZero.exp (-n) := by
      rw [hc₀_def, map_zpow₀, hπ, ← WithZero.exp_zsmul, zsmul_eq_mul]; congr 1; simp
    obtain ⟨e, he_def⟩ : ∃ e : v.adicCompletion F, e = δ * c₀ ^ 2 := ⟨_, rfl⟩
    have he : Valued.v e = 1 := by
      rw [he_def, map_mul, map_pow, hm, hvc₀, ← WithZero.exp_nsmul, ← WithZero.exp_add,
        ← WithZero.exp_zero]
      congr 1; rw [hn]; simp; ring
    have hns : ¬ IsSquare e := by
      rintro ⟨r, hr⟩
      apply hδsq
      refine ⟨r / c₀, ?_⟩
      have : δ = e / c₀ ^ 2 := by rw [he_def]; field_simp
      rw [this, hr]; ring
    have h4 : (4 : v.adicCompletion F) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 4]
      exact (map_ne_zero _).mpr (by norm_num)
    have hv4 : Valued.v (4 : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr h4
    have he1 : e - 1 ≠ 0 := by
      intro h
      apply hns
      exact ⟨1, by rw [sub_eq_zero] at h; rw [h, mul_one]⟩
    have hve1 : Valued.v (e - 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr he1
    obtain ⟨c, hc0, hc⟩ := exists_normalForm_nonsquare_unit_lemma F v π hπ
      (fun h2 => exists_sq_near_of_valuation_two_lt_one Valued.v R hR hcov h2)
      (WithZero.log (Valued.v (4 : v.adicCompletion F))) (WithZero.exp_log hv4).symm
      (WithZero.log (Valued.v (e - 1)) - WithZero.log (Valued.v (4 : v.adicCompletion F))).toNat
      e he hns (WithZero.log (Valued.v (e - 1))) (WithZero.exp_log hve1).symm (by omega)
    refine ⟨c₀ * c, mul_ne_zero hc₀0 hc0, Or.inr ?_⟩
    rw [show δ * (c₀ * c) ^ 2 = e * c ^ 2 by rw [he_def]; ring]
    exact hc
  · exact ⟨1, one_ne_zero, Or.inl ⟨n, by rw [one_pow, mul_one, hm, hn]⟩⟩

end GlobalTheory.QNorm

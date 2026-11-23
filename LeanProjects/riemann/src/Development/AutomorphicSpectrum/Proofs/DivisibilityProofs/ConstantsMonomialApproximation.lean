import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ChartForms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem isMultiHomog_chartMonomial (d : ∀ k, ι k) :
    IsMultiHomog (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) (fun _ => 1) := by
  have h := IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, d k⟩ : MRing ι ℤ)) (fun k => blockWeight ι ⟨k, d k⟩)
    (fun k _ => isWeightedHomogeneous_X ℤ _ _)
  have e : (∑ k, blockWeight ι ⟨k, d k⟩) = fun _ : K => 1 := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem isMultiHomog_mul_const {f g : MRing ι ℤ} {a b : ℕ}
    (hf : IsMultiHomog f (fun _ => a)) (hg : IsMultiHomog g (fun _ => b)) :
    IsMultiHomog (f * g) (fun _ => a + b) :=
  IsWeightedHomogeneous.mul hf hg

theorem isMultiHomog_pow_const {f : MRing ι ℤ} (hf : IsMultiHomog f (fun _ => 1)) (n : ℕ) :
    IsMultiHomog (f ^ n) (fun _ => n) := by
  induction n with
  | zero => rw [pow_zero]; exact isWeightedHomogeneous_one ℤ (blockWeight ι)
  | succ n ih => rw [pow_succ]; exact isMultiHomog_mul_const ih hf

theorem pointConeMap_chartMonomial (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) :
    pointConeMap ℤ y (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) =
      C (segreVec y d) * ∏ k : K, (X k : MvPolynomial K Ω) := by
  simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]

theorem exists_form_of_mem_chart (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hs : segreVec y c ≠ 0)
    {r : Ω} (hr : r ∈ chartRing ℤ (segreVec y) c) :
    ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧
      pointConeMap ℤ y G = C (r * segreVec y c ^ n) * (∏ k : K, (X k : MvPolynomial K Ω)) ^ n := by
  set T : MvPolynomial K Ω := ∏ k : K, (X k : MvPolynomial K Ω) with hT
  set s : Ω := segreVec y c with hsdef
  set M : MRing ι ℤ := ∏ k, X ⟨k, c k⟩ with hM
  have hMh : IsMultiHomog M (fun _ => 1) := isMultiHomog_chartMonomial c
  have hMc : pointConeMap ℤ y M = C s * T := pointConeMap_chartMonomial y c
  unfold chartRing at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    refine ⟨1, ∏ k, X ⟨k, d k⟩, isMultiHomog_chartMonomial d, ?_⟩
    rw [pointConeMap_chartMonomial, pow_one, pow_one, div_mul_cancel₀ _ hs]
  | algebraMap z =>
    refine ⟨0, C z, ?_, ?_⟩
    · exact isWeightedHomogeneous_C (blockWeight ι) z
    · have h1 : (C z : MRing ι ℤ) = algebraMap ℤ (MRing ι ℤ) z := rfl
      rw [h1, AlgHom.commutes]
      simp [MvPolynomial.algebraMap_eq]
  | add u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * M ^ b + G * M ^ a, ?_, ?_⟩
    · have h1 := isMultiHomog_mul_const hF (isMultiHomog_pow_const hMh b)
      have h2 := isMultiHomog_mul_const hG (isMultiHomog_pow_const hMh a)
      rw [add_comm b a] at h2
      exact IsWeightedHomogeneous.add h1 h2
    · simp only [map_add, map_mul, map_pow, hFc, hGc, hMc]
      ring
  | mul u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * G, isMultiHomog_mul_const hF hG, ?_⟩
    simp only [map_mul, map_pow, hFc, hGc]
    ring

theorem pointConeMap_map_int (A : Type) [CommRing A] [Algebra A Ω] (y : (Σ k, ι k) → Ω) (G : MRing ι ℤ) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) G) = pointConeMap ℤ y G := by
  induction G using MvPolynomial.induction_on with
  | C z => simp [pointConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.map_X]; simp [pointConeMap]

end ChartForms

theorem const_mul_chartMonomial_pow_form : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (c : ∀ k, ι k) (a : A), ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - (MvPolynomial.map (Int.castRingHom A) G) ∈ pointIdeal A y := by
  intro K _ _ ι _ Ω _ y A _ _ hA c a
  by_cases hs : segreVec y c = 0
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hs
    refine ⟨1, 0, isWeightedHomogeneous_zero ℤ _ _, ?_⟩
    have hX : (X ⟨k, c k⟩ : MRing ι A) ∈ pointIdeal A y := by
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hk]
    rw [map_zero, sub_zero, pow_one]
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, c k⟩ : MRing ι A)) (Finset.mem_univ k)) hX)
  · obtain ⟨n, G, hG, hGc⟩ := exists_form_of_mem_chart y c hs (hA c hs a)
    refine ⟨n, G, hG, ?_⟩
    rw [pointIdeal, RingHom.mem_ker, map_sub, pointConeMap_map_int, hGc, map_mul, map_pow]
    have hM : pointConeMap A y (∏ k, X ⟨k, c k⟩ : MRing ι A) =
        C (segreVec y c) * ∏ k : K, (X k : MvPolynomial K Ω) := by
      simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]
    have hC : pointConeMap A y (C a : MRing ι A) = C (algebraMap A Ω a) := by
      simp [pointConeMap, MvPolynomial.algebraMap_eq]
    rw [hM, hC, mul_pow, ← C_pow, C_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.Num

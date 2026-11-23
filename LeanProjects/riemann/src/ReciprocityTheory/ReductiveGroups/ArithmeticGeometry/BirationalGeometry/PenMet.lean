import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section On

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}

variable (C ι) in

structure ConeMetricOn (S : Set (ι → C)) where

  ρ : (ι → C) → ℝ
  pos : ∀ z ∈ S, 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), z ∈ S → c • z ∈ S → ρ (c • z) = ‖c‖ * ρ z

def ConeMetric.restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0) :
    ConeMetricOn C ι S where
  ρ := m.ρ
  pos z hz := m.pos z (hS z hz)
  smul c z _ _ := m.smul c z

def ptNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d

def supNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) : ℝ :=
  sSup (ptNormOn m σ d f '' S)

def IsPtsMeasureOn {S : Set (ι → ℂ)} (m : ConeMetricOn ℂ ι S) (μ : MeasureTheory.Measure (ι → ℂ)) :
    Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ (S ∩ {z | m.ρ z = 1})ᶜ = 0

def l2NormOn {S : Set (ι → ℂ)} (m : ConeMetricOn ℂ ι S) (σ : o →+* ℂ)
    (μ : MeasureTheory.Measure (ι → ℂ)) (d : ℕ) (f : MvPolynomial ι o) : ℝ :=
  Real.sqrt (∫ z, ptNormOn m σ d f z ^ 2 ∂μ)

theorem conePts_ne_zero (σ : o →+* C) (I : Ideal (MvPolynomial ι o)) :
    ∀ z ∈ conePts σ I, z ≠ 0 :=
  fun _ hz => hz.1

theorem ptNormOn_restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0)
    (σ : o →+* C) (d : ℕ) (f : MvPolynomial ι o) (z : ι → C) :
    ptNormOn (m.restrict S hS) σ d f z = ptNorm m σ d f z :=
  rfl

theorem supNormOn_restrict (m : ConeMetric C ι) (σ : o →+* C) (I : Ideal (MvPolynomial ι o))
    (d : ℕ) (f : MvPolynomial ι o) :
    supNormOn (m.restrict (conePts σ I) (conePts_ne_zero σ I)) σ d f = supNorm m σ I d f :=
  rfl

end On

section Gauss

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]

theorem ptNorm_le_ptNorm_maxMetric (h : ConeMetric C ι) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) {z : ι → C} (hz : z ≠ 0) (hle : ‖z‖ ≤ h.ρ z) :
    ptNorm h σ d f z ≤ ptNorm (maxMetric C ι) σ d f z := by
  unfold ptNorm
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos ((maxMetric C ι).pos z hz) d)
    (pow_le_pow_left₀ (norm_nonneg _) hle d)

theorem ptNorm_eq_ptNorm_maxMetric (h : ConeMetric C ι) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) {z : ι → C} (heq : ‖z‖ = h.ρ z) :
    ptNorm h σ d f z = ptNorm (maxMetric C ι) σ d f z := by
  unfold ptNorm
  rw [← heq]
  rfl

end Gauss

section Homog

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]

theorem eval_smul_of_isHomogeneousP {R : Type*} [CommRing R] {φ : MvPolynomial ι R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : ι → R) : eval (c • z) φ = c ^ d * eval z φ := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hφ (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem ptNormOn_smul {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) {d : ℕ}
    {f : MvPolynomial ι o} (hf : (map σ f).IsHomogeneous d) {c : C} (hc : c ≠ 0) {z : ι → C}
    (hz : z ∈ S) (hcz : c • z ∈ S) : ptNormOn m σ d f (c • z) = ptNormOn m σ d f z := by
  unfold ptNormOn
  rw [eval_smul_of_isHomogeneousP hf, m.smul c z hz hcz, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))

end Homog

end ReciprocityTheory.ChartRestriction.G.Geo

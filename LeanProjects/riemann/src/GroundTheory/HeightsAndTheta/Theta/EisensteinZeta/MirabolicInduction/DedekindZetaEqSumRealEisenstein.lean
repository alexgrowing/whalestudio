import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.DiscrNegAndAbsNormMul
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.DedekindZetaSeries.SummableDedekindZetaTerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace projectiveLineClassData

open NumberField UpperHalfPlane
open scoped nonZeroDivisors

section Series

def eisTerm (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : ℝ :=
  if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

theorem realEisenstein_eq_tsum (τ : ℍ) (s : ℝ) : realEisenstein τ s = ∑' p, eisTerm τ s p := rfl

theorem eisTerm_nonneg (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : 0 ≤ eisTerm τ s p := by
  unfold eisTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem summable_eisTerm (τ : ℍ) {s : ℝ} (hs : 1 < s) : Summable (eisTerm τ s) := by
  have hk : 2 < 2 * s := by linarith
  have hsum := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
    (τ.im ^ s * EisensteinSeries.r τ ^ (-(2 * s)))
  rw [← (finTwoArrowEquiv ℤ).summable_iff]
  refine Summable.of_nonneg_of_le (fun x => eisTerm_nonneg τ s _) (fun x => ?_) hsum
  have hr := EisensteinSeries.r_pos τ
  simp only [Function.comp_apply, finTwoArrowEquiv_apply, eisTerm]
  split_ifs with hx
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg τ.im_pos.le _) (Real.rpow_nonneg hr.le _))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · have hb := EisensteinSeries.summand_bound τ (by linarith : (0 : ℝ) ≤ 2 * s) x
    rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), mul_assoc]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg τ.im_pos.le _)

end Series

section IdealSum

variable (K : Type) [Field K] [NumberField K]

theorem ofReal_dedekindZetaReal {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal (GroundTheory.Global.dedekindZetaReal K s) =
      ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) := by
  classical
  rw [GroundTheory.Global.dedekindZetaReal, ENNReal.ofReal_tsum_of_nonneg
    (GroundTheory.Global.dedekindZetaTerm_nonneg K s) (ZetaSevenHalvesBounds.summable_dedekindZetaTerm K hs),
    ← ENNReal.tsum_fiberwise (fun I : Ideal (𝓞 K) => ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
      Ideal.absNorm]
  refine tsum_congr fun n => ?_
  have hfin : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))).Finite :=
    Ideal.finite_setOfPred_absNorm_eq n
  have := hfin.fintype
  rw [tsum_congr (fun I : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))) => by
    rw [show Ideal.absNorm (I : Ideal (𝓞 K)) = n from I.2]), tsum_fintype, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, GroundTheory.Global.dedekindZetaTerm,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← Nat.card_eq_fintype_card]
  rfl

theorem tsum_ideal_eq_sum_class {s : ℝ} (hs : 0 < s) :
    ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) =
      ∑ B : ClassGroup (𝓞 K), ∑' I : (ClassGroup.mk0 ⁻¹' {B} : Set (Ideal (𝓞 K))⁰),
        ENNReal.ofReal ((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
  classical
  have hsupp : Function.support (fun I : Ideal (𝓞 K) => ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
      ⊆ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) := by
    intro I hI
    rw [SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero]
    rintro rfl
    apply hI
    simp [Ideal.absNorm_bot, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  change ∑' x : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((Ideal.absNorm (x : Ideal (𝓞 K)) : ℝ) ^ (-s)) = _
  rw [← ENNReal.tsum_fiberwise _ (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K)), tsum_fintype]

end IdealSum

section ClassSum

variable {K : Type} [Field K] [NumberField K]

open FractionalIdeal EtaPeriodLatticeClass

local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem spanSingleton_mul_inv_le_one (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K}
    (hx : x ∈ (↑ᶠ J)) : spanSingleton (𝓞 K)⁰ x * (↑ᶠ J⁻¹) ≤ 1 := by
  rw [spanSingleton_mul_le_iff]
  intro z hz
  have h := mul_mem_mul hx hz
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one] at h

def idealOf (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) : Ideal (𝓞 K) :=
  (le_one_iff_exists_coeIdeal.mp (spanSingleton_mul_inv_le_one J hx)).choose

theorem coe_idealOf (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) :
    ((idealOf J hx : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ x * (↑ᶠ J⁻¹) :=
  (le_one_iff_exists_coeIdeal.mp (spanSingleton_mul_inv_le_one J hx)).choose_spec

theorem idealOf_mem (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) (hx0 : x ≠ 0) :
    idealOf J hx ∈ (Ideal (𝓞 K))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have h2 := coe_idealOf J hx
  rw [h, Ideal.zero_eq_bot, coeIdeal_bot] at h2
  exact mul_ne_zero (spanSingleton_ne_zero_iff.mpr hx0) (Units.ne_zero _) h2.symm

theorem class_idealOf_eq_inv_class (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) (hx0 : x ≠ 0) :
    ClassGroup.mk0 ⟨idealOf J hx, idealOf_mem J hx hx0⟩ = (ClassGroup.mk K J)⁻¹ := by
  rw [← ClassGroup.mk_mk0 K]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, ClassGroup.mk_eq_one_iff, Units.val_mul, FractionalIdeal.coe_mk0, coe_idealOf,
    mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, coe_spanSingleton]
  exact ⟨⟨x, rfl⟩⟩

abbrev Nz (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type := {x : K // x ∈ (↑ᶠ J) ∧ x ≠ 0}

abbrev InvClassIdeals (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type :=
  ((ClassGroup.mk0 ⁻¹' {(ClassGroup.mk K J)⁻¹} : Set (Ideal (𝓞 K))⁰))

def psi (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) : InvClassIdeals J :=
  ⟨⟨idealOf J x.2.1, idealOf_mem J x.2.1 x.2.2⟩, class_idealOf_eq_inv_class J x.2.1 x.2.2⟩

theorem coe_psi (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (x : K) * (↑ᶠ J⁻¹) :=
  coe_idealOf J x.2.1

theorem psi_eq_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : Nz J) :
    psi J x = psi J y ↔ spanSingleton (𝓞 K)⁰ (x : K) = spanSingleton (𝓞 K)⁰ (y : K) := by
  constructor
  · intro h
    have h2 := congrArg (fun t : InvClassIdeals J =>
      (((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) h
    simp only [coe_psi] at h2
    exact mul_right_cancel₀ (Units.ne_zero _) h2
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply coeIdeal_injective (K := K)
    change (((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      (((psi J y : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [coe_psi, coe_psi, h]

theorem psi_surjective (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (psi J) := by
  rintro ⟨⟨I, hI⟩, hcl⟩
  have hcl' : ClassGroup.mk0 ⟨I, hI⟩ = (ClassGroup.mk K J)⁻¹ := hcl
  have h1 : ClassGroup.mk K (FractionalIdeal.mk0 K ⟨I, hI⟩ * J) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hcl', inv_mul_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  set P := FractionalIdeal.mk0 K ⟨I, hI⟩ * J with hP
  have hPval : (P : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) := by
    rw [hP, Units.val_mul, FractionalIdeal.coe_mk0]
  have hgen := FractionalIdeal.eq_spanSingleton_of_principal (P : FractionalIdeal (𝓞 K)⁰ K)
  set x := Submodule.IsPrincipal.generator ((P : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  have hxP : x ∈ (P : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hgen]; exact mem_spanSingleton_self _ _
  have hxJ : x ∈ (↑ᶠ J) := by
    rw [hPval] at hxP
    have hle : (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) ≤ (↑ᶠ J) := by
      calc (I : FractionalIdeal (𝓞 K)⁰ K) * (↑ᶠ J) ≤ 1 * (↑ᶠ J) := by
            rw [FractionalIdeal.mul_le]
            intro i hi j hj
            exact mul_mem_mul (coeIdeal_le_one hi) hj
        _ = (↑ᶠ J) := one_mul _
    exact hle hxP
  have hx0 : x ≠ 0 := by
    intro h0
    have : (P : FractionalIdeal (𝓞 K)⁰ K) = 0 := by rw [hgen, h0, spanSingleton_zero]
    exact Units.ne_zero P this
  refine ⟨⟨x, hxJ, hx0⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply coeIdeal_injective (K := K)
  change (((psi J ⟨x, hxJ, hx0⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [coe_psi, ← hgen, hPval, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end ClassSum

section Fibres

variable {K : Type} [Field K] [NumberField K]

open FractionalIdeal

local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

def unitMul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) (u : (𝓞 K)ˣ) : Nz J :=
  ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * x₀, by
    have h := Submodule.smul_mem ((↑ᶠ J) : Submodule (𝓞 K) K) (u : 𝓞 K) (mem_coe.mpr x₀.2.1)
    rw [Algebra.smul_def] at h
    exact mem_coe.mp h,
   mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr u.ne_zero) x₀.2.2⟩

theorem psi_unitMul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) (u : (𝓞 K)ˣ) :
    psi J (unitMul J x₀ u) = psi J x₀ := by
  rw [psi_eq_iff, eq_comm, spanSingleton_eq_spanSingleton]
  exact ⟨u, by rw [Units.smul_def, Algebra.smul_def]; rfl⟩

def fiberEquiv (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) :
    (𝓞 K)ˣ ≃ (psi J ⁻¹' {psi J x₀}) :=
  Equiv.ofBijective (fun u => ⟨unitMul J x₀ u, psi_unitMul J x₀ u⟩) (by
    constructor
    · intro u v h
      have h2 := congrArg (fun y : (psi J ⁻¹' {psi J x₀}) => ((y : Nz J) : K)) h
      simp only [unitMul] at h2
      have h3 := mul_right_cancel₀ x₀.2.2 h2
      exact Units.ext (IsFractionRing.injective (𝓞 K) K h3)
    · rintro ⟨y, hy⟩
      have hy' : psi J y = psi J x₀ := hy
      rw [psi_eq_iff, eq_comm, spanSingleton_eq_spanSingleton] at hy'
      obtain ⟨z, hz⟩ := hy'
      refine ⟨z, Subtype.ext (Subtype.ext ?_)⟩
      rw [← hz, Units.smul_def, Algebra.smul_def]
      rfl)

theorem tsum_psi (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InvClassIdeals J → ENNReal) :
    ∑' x : Nz J, g (psi J x) = (Units.torsionOrder K : ENNReal) * ∑' t, g t := by
  classical
  have hcard := natCard_units hK σ hσ
  have hfin : Finite (𝓞 K)ˣ :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Units.torsionOrder_ne_zero K)
  have := Fintype.ofFinite (𝓞 K)ˣ
  rw [← ENNReal.tsum_fiberwise (fun x => g (psi J x)) (psi J), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  obtain ⟨x₀, rfl⟩ := psi_surjective J t
  rw [tsum_congr (fun y : (psi J ⁻¹' {psi J x₀}) => by
      rw [show psi J (y : Nz J) = psi J x₀ from y.2]),
    ← (fiberEquiv J x₀).tsum_eq, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, hcard]

end Fibres

section Lattice

variable {K : Type} [Field K] [NumberField K]

open FractionalIdeal EtaPeriodLatticeClass

local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem absNorm_psi (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) =
      ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) := by
  have h1 := congrArg FractionalIdeal.absNorm (coe_psi J x)
  rw [coeIdeal_absNorm, map_mul, absNorm_span_singleton] at h1
  have hinv : FractionalIdeal.absNorm (↑ᶠ J⁻¹) = (FractionalIdeal.absNorm (↑ᶠ J))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [hinv] at h1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs, Rat.cast_inv] at h2
  rw [h2, abs_norm_eq hK σ hσ, div_eq_mul_inv]

theorem rpow_identity {n q y : ℝ} (hn : 0 < n) (hq : 0 < q) (hy : 0 < y) (s : ℝ) :
    (n ^ 2 * q / (2 * y)) ^ (-s) = (2 / q) ^ s * (y ^ s / n ^ (2 * s)) := by
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  have h : (n ^ 2 * q / (2 * y))⁻¹ = (2 / q) * (y / n ^ 2) := by
    rw [inv_div]
    field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.div_rpow hy.le (by positivity),
    show (2 : ℝ) * s = ((2 : ℕ) : ℝ) * s by norm_num, Real.rpow_natCast_mul hn.le]

abbrev NzPair : Type := {p : ℤ × ℤ // p ≠ 0}

abbrev NzLattice (τ : ℍ) : Type := {z : ℂ // z ∈ latticeOf (τ : ℂ) ∧ z ≠ 0}

def pairToLattice (τ : ℍ) (p : NzPair) : NzLattice τ :=
  ⟨p.1.1 * τ + p.1.2, mem_latticeOf.mpr ⟨p.1.2, p.1.1, by ring⟩, by
    intro h
    apply p.2
    have := coord_unique (τ := τ) (m := p.1.2) (n := p.1.1) (m' := 0) (n' := 0)
      (by push_cast; linear_combination h)
    exact Prod.ext this.2 this.1⟩

theorem pairToLattice_bijective (τ : ℍ) : Function.Bijective (pairToLattice τ) := by
  constructor
  · intro p r h
    have h2 := congrArg (fun z : NzLattice τ => (z : ℂ)) h
    simp only [pairToLattice] at h2
    have := coord_unique (τ := τ) (m := p.1.2) (n := p.1.1) (m' := r.1.2) (n' := r.1.1)
      (by linear_combination h2)
    exact Subtype.ext (Prod.ext this.2 this.1)
  · rintro ⟨z, hz, hz0⟩
    obtain ⟨m, n, rfl⟩ := mem_latticeOf.mp hz
    refine ⟨⟨(n, m), fun h => hz0 ?_⟩, Subtype.ext ?_⟩
    · rw [Prod.mk_eq_zero] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · simp only [pairToLattice]
      ring

def eltToLattice (σ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) (x : Nz J) :
    NzLattice τ :=
  ⟨c * σ x, by rw [← himg]; exact ⟨σ x, ⟨x, x.2.1, rfl⟩, rfl⟩,
    mul_ne_zero hc ((map_ne_zero σ).mpr x.2.2)⟩

theorem eltToLattice_bijective (σ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ)
    (hc : c ≠ 0) (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) :
    Function.Bijective (eltToLattice σ J τ c hc himg) := by
  constructor
  · intro x y h
    have h2 := congrArg (fun z : NzLattice τ => (z : ℂ)) h
    simp only [eltToLattice] at h2
    exact Subtype.ext (σ.injective (mul_left_cancel₀ hc h2))
  · rintro ⟨z, hz, hz0⟩
    rw [← himg] at hz
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    refine ⟨⟨x, hx, fun h => hz0 (by simp [h])⟩, rfl⟩

theorem class_sum (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) {s : ℝ}
    (hs : 1 < s) :
    (Units.torsionOrder K : ENNReal) * ∑' t : InvClassIdeals J,
        ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
      ENNReal.ofReal ((2 / Real.sqrt |(discr K : ℝ)|) ^ s * realEisenstein τ s) := by
  rw [← tsum_psi hK σ hσ J (fun t => ENNReal.ofReal
    ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))]
  obtain ⟨hD, hcov⟩ := discr_neg_and_absNorm_mul hK σ hσ (↑ᶠ J) τ c hc himg
  set q := Real.sqrt |(discr K : ℝ)| with hqdef
  have hq : 0 < q := Real.sqrt_pos.mpr (abs_pos.mpr hD.ne)
  have hy := τ.im_pos
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set F : NzLattice τ → ENNReal :=
    fun z => ENNReal.ofReal ((2 / q) ^ s * (τ.im ^ s / ‖(z : ℂ)‖ ^ (2 * s))) with hF
  have hterm : ∀ x : Nz J, ENNReal.ofReal
      ((Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
        F (eltToLattice σ J τ c hc himg x) := by
    intro x
    rw [absNorm_psi hK σ hσ J x, hF]
    congr 1
    have hx0 : σ (x : K) ≠ 0 := (map_ne_zero σ).mpr x.2.2
    have hN : ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) = 2 * τ.im / (q * ‖c‖ ^ 2) := by
      rw [eq_div_iff (by positivity)]
      rw [eq_div_iff hq.ne'] at hcov
      linear_combination hcov
    have h3 : ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) =
        ‖c * σ (x : K)‖ ^ 2 * q / (2 * τ.im) := by
      rw [hN, norm_mul]
      field_simp
    rw [h3]
    exact rpow_identity (norm_pos_iff.mpr (mul_ne_zero hc hx0)) hq hy s
  rw [tsum_congr hterm]
  have e1 := (Equiv.ofBijective _ (eltToLattice_bijective σ J τ c hc himg)).tsum_eq F
  simp only [Equiv.ofBijective_apply] at e1
  rw [e1]
  have e2 := (Equiv.ofBijective _ (pairToLattice_bijective τ)).tsum_eq F
  simp only [Equiv.ofBijective_apply] at e2
  rw [← e2]
  have hG : ∀ p : NzPair, F (pairToLattice τ p) =
      ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p.1) := by
    intro p
    simp only [hF, pairToLattice, eisTerm, if_neg p.2]
  rw [tsum_congr hG]
  have hsupp : Function.support (fun p : ℤ × ℤ => ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p)) ⊆
      {p | p ≠ 0} := by
    intro p hp h0
    apply hp
    have h0' : p = 0 := by simpa using h0
    simp [h0', eisTerm]
  have e3 := tsum_subtype_eq_of_support_subset hsupp
  change ∑' p : {p : ℤ × ℤ // p ≠ 0}, _ = _
  rw [show (∑' p : {p : ℤ × ℤ // p ≠ 0}, ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p.1)) =
    ∑' p : ({p | p ≠ 0} : Set (ℤ × ℤ)), ENNReal.ofReal ((2 / q) ^ s * eisTerm τ s p) from rfl, e3,
    ← ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg (by positivity) (eisTerm_nonneg τ s p))
      ((summable_eisTerm τ hs).mul_left _), tsum_mul_left, realEisenstein_eq_tsum]

end Lattice

section Main

theorem dedekindZeta_eq_sum_realEisenstein {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (τ : ClassGroup (𝓞 K) → ℍ)
    (hτ : ∀ A, ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = A ∧
      IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) (τ A))
    {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta K s =
      (((NumberField.Units.torsionOrder K : ℝ)⁻¹ * (2 / Real.sqrt |(NumberField.discr K : ℝ)|) ^ s *
        ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s : ℝ) : ℂ) := by
  classical
  rw [GroundTheory.Global.dedekindZeta_ofReal K (by linarith : s ≠ 0)]
  congr 1
  set q := Real.sqrt |(discr K : ℝ)| with hqdef
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hcl : ∀ A : ClassGroup (𝓞 K),
      ∑' t : (ClassGroup.mk0 ⁻¹' {A⁻¹} : Set (Ideal (𝓞 K))⁰),
        ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
      ENNReal.ofReal ((Units.torsionOrder K : ℝ)⁻¹ * ((2 / q) ^ s * realEisenstein (τ A) s)) := by
    intro A
    obtain ⟨J, hJ, c, hc, himg⟩ := hτ A
    have h := class_sum hK σ hσ J (τ A) c hc himg hs
    subst hJ
    have hw0 : (Units.torsionOrder K : ENNReal) ≠ 0 := by
      exact_mod_cast (Units.torsionOrder_ne_zero K)
    have hwt : (Units.torsionOrder K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hw.le), ENNReal.ofReal_inv_of_pos hw,
      ENNReal.ofReal_natCast, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff hw0 hwt]
    exact h
  have hnn : ∀ A : ClassGroup (𝓞 K),
      0 ≤ (Units.torsionOrder K : ℝ)⁻¹ * ((2 / q) ^ s * realEisenstein (τ A) s) := fun A =>
    mul_nonneg (inv_nonneg.mpr hw.le) (mul_nonneg (by positivity) (realEisenstein_nonneg _ _))
  have hmain : ENNReal.ofReal (GroundTheory.Global.dedekindZetaReal K s) =
      ENNReal.ofReal ((Units.torsionOrder K : ℝ)⁻¹ * (2 / q) ^ s *
        ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s) := by
    rw [ofReal_dedekindZetaReal K hs, tsum_ideal_eq_sum_class K (by linarith),
      (Fintype.sum_equiv (Equiv.inv (ClassGroup (𝓞 K)))
        (fun A => ∑' t : (ClassGroup.mk0 ⁻¹' {A⁻¹} : Set (Ideal (𝓞 K))⁰),
          ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))
        (fun B => ∑' t : (ClassGroup.mk0 ⁻¹' {B} : Set (Ideal (𝓞 K))⁰),
          ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)))
        (fun A => rfl)).symm]
    rw [Finset.sum_congr rfl (fun A _ => hcl A), ← ENNReal.ofReal_sum_of_nonneg (fun A _ => hnn A),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun A _ => ?_
    ring
  have h0 : 0 ≤ GroundTheory.Global.dedekindZetaReal K s :=
    tsum_nonneg (GroundTheory.Global.dedekindZetaTerm_nonneg K s)
  have h1 : 0 ≤ (Units.torsionOrder K : ℝ)⁻¹ * (2 / q) ^ s *
      ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hw.le) (by positivity))
      (Finset.sum_nonneg fun A _ => realEisenstein_nonneg _ _)
  exact (ENNReal.ofReal_eq_ofReal_iff h0 h1).mp hmain

end Main

end projectiveLineClassData

end GroundTheory.Heights₂.Theta

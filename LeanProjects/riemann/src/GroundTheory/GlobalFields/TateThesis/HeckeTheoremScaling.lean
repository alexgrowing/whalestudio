import Mathlib
import GroundTheory.GlobalFields.TateThesis.TateMainUnique
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourier

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem ofReal_inv_cpow_of_pos {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), cpow_neg]

theorem globalZeta_comp_smul (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (a : IdeleGroup K) (s : ℂ) :
    globalZeta (fun y ↦ F (a • y)) χ s =
      (χ.toIdele a : ℂ)⁻¹ * ((ideleModule K a : ℝ) : ℂ) ^ (-s) * globalZeta F χ s := by
  unfold globalZeta
  have h := integral_mul_left_eq_self (μ := ideleMeasure K)
    (fun x : IdeleGroup K ↦ F (a • (x : 𝔸[K])) * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s) a⁻¹
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have h1 : a • ((a⁻¹ * x : IdeleGroup K) : 𝔸[K]) = (x : 𝔸[K]) := by
    rw [Units.smul_def, smul_eq_mul, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : ((ideleModule K (a⁻¹ * x) : ℝ) : ℂ) ^ s =
      ((ideleModule K a : ℝ) : ℂ) ^ (-s) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    rw [map_mul, map_inv, Positive.val_mul, Positive.coe_inv, ofReal_mul,
      mul_cpow_ofReal_nonneg (inv_nonneg.2 (ideleModule K a).2.le) (ideleModule K x).2.le,
      ofReal_inv_cpow_of_pos (ideleModule K a).2]
  beta_reduce
  rw [h1, h2]
  simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
  ring

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def discrNormConductor : ℝ := |(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ)

theorem discrNormConductor_pos : 0 < χ.discrNormConductor := by
  refine mul_pos (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))) (Nat.cast_pos.2 ?_)
  exact Nat.pos_of_ne_zero fun h ↦ χ.conductor_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem discrNormConductor_inv : χ⁻¹.discrNormConductor = χ.discrNormConductor := by
  rw [discrNormConductor, discrNormConductor, conductor_inv]

theorem ideleModule_ofFinite_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    (ideleModule K (ofFinite δ) : ℝ) = χ.discrNormConductor⁻¹ := by
  have hI : χ.conductor * differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
    mul_ne_zero χ.conductor_ne_bot differentIdeal_ne_bot
  have hunit : idealUnit χ.conductor χ.conductor_ne_bot * differentUnit = idealUnit _ hI := by
    ext
    simp [idealUnit, differentUnit, FractionalIdeal.coeIdeal_mul]
  have hpos : ∀ v, 0 ≤ ord v (ofFinite δ) := fun v ↦ by
    rw [← count_toFractionalIdeal, hδ, hunit]
    change 0 ≤ FractionalIdeal.count K v
      (((χ.conductor * differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K))) : FractionalIdeal (𝓞 K)⁰ K)
    rw [count_coeIdeal_eq_multiplicity v hI]
    positivity
  have hideal : idealOfExponents (ordFinsupp K (ofFinite δ)) =
      χ.conductor * differentIdeal ℤ (𝓞 K) := by
    have h1 : toFractionalIdeal (ofFinite δ) =
        idealUnit _ (idealOfExponents_ne_bot (K := K) (n := ordFinsupp K (ofFinite δ)) hpos) := by
      rw [toFractionalIdeal_eq_iff]
      intro v
      exact (count_idealOfExponents (n := ordFinsupp K (ofFinite δ)) hpos v).symm
    rw [hδ, hunit] at h1
    exact FractionalIdeal.coeIdeal_injective (K := K) (congrArg Units.val h1).symm
  have hinf : infiniteModule (ofFinite δ) = 1 := by
    have e : ((ofFinite δ : IdeleGroup K) : 𝔸[K]).1 = 1 := by
      change ((toInfinite K (ofFinite δ) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1
      rw [toInfinite_ofFinite, Units.val_one]
    simp only [infiniteModule, e]
    exact Finset.prod_eq_one fun w _ ↦ by
      rw [show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, hinf, one_mul, finiteModule_ofFinite_eq hpos, hideal, map_mul,
    absNorm_differentIdeal K (𝓞 K), discrNormConductor, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs,
    mul_comm]

theorem globalZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (s : ℂ) :
    globalZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        globalZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hf : adelicFourier K χ.testFunction =
      fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) :=
    funext (χ.adelicFourier_testFunction hδ)
  have h1 : globalZeta (fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s =
      χ.fourierConst δ * globalZeta (fun y ↦ (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s := by
    unfold globalZeta
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hf, h1, globalZeta_comp_smul, χ.ideleModule_ofFinite_of_toFractionalIdeal_eq hδ,
    ofReal_inv_cpow_of_pos χ.discrNormConductor_pos, neg_neg, χ.inv_toIdele, Circle.coe_inv, inv_inv]
  ring

theorem exists_inv_ne_one (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    ∃ v : normOneSubgroup K, χ⁻¹.toIdele (v : IdeleGroup K) ≠ 1 := by
  obtain ⟨v, hv⟩ := hχ
  exact ⟨v, by rw [χ.inv_toIdele, ne_eq, inv_eq_one]; exact hv⟩

theorem inv_eq_cpow_of_forall {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∀ x : IdeleGroup K,
      ((χ⁻¹).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((-τ : ℝ) : ℂ) * I) := fun x ↦ by
  rw [χ.inv_toIdele, Circle.coe_inv, hτ, ← cpow_neg]
  push_cast
  ring_nf

theorem differentiable_const_cpow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) : Differentiable ℂ fun s ↦ c * (r : ℂ) ^ s * f s :=
  ((differentiable_const c).mul
    (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 hr.ne')))).mul hf

theorem tateZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) (s : ℂ) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hχ' := χ.exists_inv_ne_one hχ
  have h := eq_tateZeta_of_differentiable (adelicFourier_mem_schwartzBruhat χ.testFunction_mem) hχ'
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (differentiable_const_cpow_mul (differentiable_tateZeta (χ⁻¹).testFunction_mem hχ') _
      χ.discrNormConductor_pos)
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (congrFun h s).symm

theorem tateZeta_adelicFourier_testFunction_of_forall {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {s : ℂ} (hs₀ : s ≠ (τ : ℂ) * I) (hs₁ : s ≠ 1 + (τ : ℂ) * I) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hτ' := χ.inv_eq_cpow_of_forall hτ
  have hpole : ∀ z : ℂ, z ≠ (τ : ℂ) * I → z ≠ 1 + (τ : ℂ) * I →
      z ≠ -(((-τ : ℝ) : ℂ) * I) ∧ z ≠ 1 - ((-τ : ℝ) : ℂ) * I := fun z h0 h1 ↦ by
    push_cast
    constructor
    · rw [neg_mul, neg_neg]; exact h0
    · rw [neg_mul, sub_neg_eq_add]; exact h1
  have hmem : s ∈ ({-(((-τ : ℝ) : ℂ) * I), 1 - ((-τ : ℝ) : ℂ) * I} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact hpole s hs₀ hs₁
  have h := eqOn_tateZeta_of_differentiableOn hτ'
    (adelicFourier_mem_schwartzBruhat χ.testFunction_mem)
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (fun z hz ↦ by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((differentiableAt_const _).mul ((differentiableAt_id).const_cpow
        (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul
        (differentiableAt_tateZeta hτ' (χ⁻¹).testFunction_mem hz.1 hz.2))
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (h hmem).symm

end HeckeCharacter

end

end GroundTheory.Global

import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldHecke

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra Parabolic AddMonoidAlgebra Finset
open scoped ValuativeRel Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

noncomputable local instance fintypeResidue' : Fintype 𝓀[F] := Fintype.ofFinite _

theorem sphericalFun_mul_right {χ : levi F n (id : Fin n → Fin n) →* ℂ} (hχ : IsUnramified χ)
    (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    sphericalFun χ (g * k) = sphericalFun χ g := by
  obtain ⟨b, k', hk', rfl⟩ := exists_borel_mul g
  rw [mul_assoc, sphericalFun_mul hχ _ (mul_mem hk' hk), sphericalFun_mul hχ _ hk']

theorem sphericalFun_of_mem {χ : levi F n (id : Fin n → Fin n) →* ℂ} (hχ : IsUnramified χ)
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) : sphericalFun χ k = 1 := by
  rw [← one_mul k, sphericalFun_mul_right hχ 1 hk, sphericalFun_one hχ]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integral_mul_sphericalFun (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n))
    (y : GL (Fin n) F) :
    ∫ x, (h : HeckeAlgebra μ) x * sphericalFun (paramChar F z) (y * x) ∂μ =
      evalAt z (satakeTransform μ h) * sphericalFun (paramChar F z) y := by
  have hχ := isUnramified_paramChar (F := F) z
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n))
    (charRep (paramChar F z))
  let ev : Module.Dual ℂ (principalSeriesSpace F n (paramChar F z)) :=
    (LinearMap.proj y).comp (principalSeriesSpace F n (paramChar F z)).subtype
  have h1 := dual_heckeAct μ (h : HeckeAlgebra μ).mem (hs (sphericalVector hχ)) ev
  rw [heckeAct_sphericalVector, map_smul] at h1
  simp only [ev, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
    LinearMap.coe_proj, Function.eval, coe_sphericalVector, smul_eq_mul] at h1
  rw [← sphericalCharacter_paramChar z h, sphericalCharacter_apply, h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [coe_indRep_apply]
  rfl

theorem sum_sphericalFun_gMat (z : Fin n → ℂˣ) (r : ℕ) (y : GL (Fin n) F) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F],
        sphericalFun (paramChar F z) (y * gMat S c) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ *
        evalAt z (satakeTransform μ (minusculeHecke μ r)) * sphericalFun (paramChar F z) y := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 := integral_minusculeHecke_mul (μ := μ)
    (fun g k hk => sphericalFun_mul_right (isUnramified_paramChar z) g hk) y r
  rw [integral_mul_sphericalFun] at h1
  rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]

variable (μ) in

def zonalSpherical (z : Fin n → ℂˣ) (g : GL (Fin n) F) : ℂ :=
  (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ *
    ∫ x, (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * g) ∂μ

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem isClopen_integralGL : IsClopen (integralGL F n : Set (GL (Fin n) F)) :=
  ⟨(isCompact_integralGL F n).isClosed, isOpen_integralGL F n⟩

theorem integrable_indicator_mul_sphericalFun (z : Fin n → ℂˣ) (g : GL (Fin n) F) :
    Integrable (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * g)) μ := by
  have hφ : Continuous (sphericalFun (paramChar F z)) :=
    continuous_of_mul_right_invariant fun g k hk => sphericalFun_mul_right (isUnramified_paramChar z) g hk
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (isClopen_integralGL.continuous_indicator continuous_const).mul
      (hφ.comp (continuous_mul_right g))
  · refine HasCompactSupport.intro (isCompact_integralGL F n) fun x hx => ?_
    simp only [Set.indicator_of_notMem hx, zero_mul]

theorem zonalSpherical_mul_right (z : Fin n → ℂˣ) (g : GL (Fin n) F) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) : zonalSpherical μ z (g * k) = zonalSpherical μ z g := by
  simp only [zonalSpherical, ← mul_assoc,
    sphericalFun_mul_right (isUnramified_paramChar z) _ hk]

theorem zonalSpherical_mul_left (z : Fin n → ℂˣ) {k : GL (Fin n) F} (hk : k ∈ integralGL F n)
    (g : GL (Fin n) F) : zonalSpherical μ z (k * g) = zonalSpherical μ z g := by
  haveI := Measures.isMulRightInvariant_GL F n μ
  simp only [zonalSpherical]
  congr 1
  have h := integral_mul_right_eq_self (μ := μ)
    (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) (x * k⁻¹) *
      sphericalFun (paramChar F z) (x * g)) k
  simp only [mul_inv_cancel_right] at h
  rw [show (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * (k * g))) = fun x =>
      (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * k * g) by simp only [mul_assoc], h]
  congr 1
  funext x
  congr 1
  have : x * k⁻¹ ∈ integralGL F n ↔ x ∈ integralGL F n :=
    ⟨fun h => by simpa using mul_mem h hk, fun h => mul_mem h ((integralGL F n).inv_mem hk)⟩
  by_cases hx : x ∈ integralGL F n
  · rw [Set.indicator_of_mem (show x * k⁻¹ ∈ (integralGL F n : Set (GL (Fin n) F)) from this.2 hx),
      Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx)]
  · rw [Set.indicator_of_notMem (show x * k⁻¹ ∉ (integralGL F n : Set (GL (Fin n) F)) from
      fun h => hx (this.1 h)),
      Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx)]

theorem zonalSpherical_one (z : Fin n → ℂˣ) : zonalSpherical μ z 1 = 1 := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rw [zonalSpherical]
  have : (fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ)) x *
      sphericalFun (paramChar F z) (x * 1)) =
      fun x => (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => ((1 : ℝ) : ℂ)) x := by
    funext x
    by_cases hx : x ∈ integralGL F n
    · rw [Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), mul_one,
        sphericalFun_of_mem (isUnramified_paramChar z) hx, one_mul, Complex.ofReal_one]
    · rw [Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), zero_mul]
  rw [this, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, Complex.ofReal_one, mul_one]
  exact inv_mul_cancel₀ hK

theorem zonalSpherical_torusPow_comp (z : Fin n → ℂˣ) (μ' : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    zonalSpherical μ z (torusPow F n (μ' ∘ σ)) = zonalSpherical μ z (torusPow F n μ') := by
  rw [← permGL_conj_torusPow, zonalSpherical_mul_right z _ (permGL_mem_integralGL F n σ),
    zonalSpherical_mul_left z ((integralGL F n).inv_mem (permGL_mem_integralGL F n σ))]

theorem sum_zonalSpherical_gMat (z : Fin n → ℂˣ) (r : ℕ) (g : GL (Fin n) F) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[F],
        zonalSpherical μ z (g * gMat S c) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ *
        evalAt z (satakeTransform μ (minusculeHecke μ r)) * zonalSpherical μ z g := by
  set c₀ := (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹
  set ind := (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (1 : ℂ))
  set P := (Finset.univ : Finset (Fin n)).powersetCard r
  have hint : ∀ g' : GL (Fin n) F,
      Integrable (fun x => ind x * sphericalFun (paramChar F z) (x * g')) μ :=
    fun g' => integrable_indicator_mul_sphericalFun z g'
  have e1 : (∑ S ∈ P, ∑ c : Pairs S → 𝓀[F],
      ∫ x, ind x * sphericalFun (paramChar F z) (x * (g * gMat S c)) ∂μ) =
      ∫ x, ∑ S ∈ P, ∑ c : Pairs S → 𝓀[F],
        ind x * sphericalFun (paramChar F z) (x * (g * gMat S c)) ∂μ := by
    have e := integral_finsetSum (μ := μ) (f := fun S x => ∑ c : Pairs S → 𝓀[F],
      ind x * sphericalFun (paramChar F z) (x * (g * gMat S c))) P
      (fun S _ => integrable_finset_sum _ fun c _ => hint _)
    rw [e]
    refine Finset.sum_congr rfl fun S _ => ?_
    have e' := integral_finsetSum (μ := μ) (f := fun c x =>
      ind x * sphericalFun (paramChar F z) (x * (g * gMat S c))) Finset.univ (fun c _ => hint _)
    rw [e']
  have e2 : ∀ x, ∑ S ∈ P, ∑ c : Pairs S → 𝓀[F],
      ind x * sphericalFun (paramChar F z) (x * (g * gMat S c)) =
      c₀ * evalAt z (satakeTransform μ (minusculeHecke μ r)) *
        (ind x * sphericalFun (paramChar F z) (x * g)) := by
    intro x
    simp only [← Finset.mul_sum, ← mul_assoc x g]
    rw [sum_sphericalFun_gMat (μ := μ)]
    ring
  simp only [zonalSpherical, ← Finset.mul_sum]
  rw [e1]
  simp_rw [e2]
  rw [integral_const_mul]
  ring

theorem zonalSpherical_recursion (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) {r : ℕ}
    (hr : r ≤ n) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * zonalSpherical μ z (torusPow F n l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * zonalSpherical μ z (torusPow F n (l + lamS S)) := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 := sum_zonalSpherical_gMat (μ := μ) z r (torusPow F n l)
  rw [evalAt_satakeTransform_minusculeHecke z hr] at h1
  rw [← Finset.sum_congr rfl fun S _ => sum_gMat_torusPow (f := zonalSpherical μ z)
    (fun u hu g => zonalSpherical_mul_left z hu.2 g) hl S, h1]
  field_simp

theorem recursion_of_integral_eq (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hfK : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hfN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, f (u * g) = f g)
    {l : Fin n → ℤ} (hl : Antitone l) {r : ℕ} (hr : r ≤ n)
    (heig : ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * f (torusPow F n l * x) ∂μ =
      evalAt z (satakeTransform μ (minusculeHecke μ r)) * f (torusPow F n l)) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f (torusPow F n l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * f (torusPow F n (l + lamS S)) := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rw [integral_minusculeHecke_mul hfK, evalAt_satakeTransform_minusculeHecke z hr] at heig
  rw [← Finset.sum_congr rfl fun S _ => sum_gMat_torusPow hfN hl S]
  apply mul_left_cancel₀ hK
  rw [heig]
  ring

end Spherical

end GroundTheory.Automorphic

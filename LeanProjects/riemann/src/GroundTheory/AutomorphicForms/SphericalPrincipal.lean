import Mathlib
import GroundTheory.AutomorphicForms.SphericalCommutative
import GroundTheory.AutomorphicForms.InductionParabolic

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def IsUnramified (χ : levi F n (id : Fin n → Fin n) →* ℂ) : Prop :=
  ∀ t : levi F n (id : Fin n → Fin n), (t : GL (Fin n) F) ∈ integralGL F n → χ t = 1

def charRep (χ : levi F n (id : Fin n → Fin n) →* ℂ) :
    Representation ℂ (levi F n (id : Fin n → Fin n)) ℂ :=
  twist χ (Representation.trivial ℂ _ ℂ)

@[simp]
theorem charRep_apply (χ : levi F n (id : Fin n → Fin n) →* ℂ) (t : levi F n (id : Fin n → Fin n))
    (z : ℂ) : charRep χ t z = χ t * z := by
  simp [charRep]

variable (F n) in

abbrev principalSeriesSpace (χ : levi F n (id : Fin n → Fin n) →* ℂ) :
    Submodule ℂ (GL (Fin n) F → ℂ) :=
  parabolicIndSpace F n (id : Fin n → Fin n) (charRep χ)

variable (F n) in

abbrev principalSeries (χ : levi F n (id : Fin n → Fin n) →* ℂ) :
    Representation ℂ (GL (Fin n) F) (principalSeriesSpace F n χ) :=
  parabolicInd F n (id : Fin n → Fin n) (charRep χ)

def borelChar (χ : levi F n (id : Fin n → Fin n) →* ℂ) : blockUpper F n (id : Fin n → Fin n) →* ℂ where
  toFun p := sqrtModular F n id p * χ (leviProj F n id p)
  map_one' := by simp
  map_mul' p q := by
    simp only [map_mul]
    ring

theorem borelChar_apply (χ : levi F n (id : Fin n → Fin n) →* ℂ)
    (p : blockUpper F n (id : Fin n → Fin n)) :
    borelChar χ p = sqrtModular F n id p * χ (leviProj F n id p) := rfl

theorem mem_principalSeriesSpace {χ : levi F n (id : Fin n → Fin n) →* ℂ} {f : GL (Fin n) F → ℂ} :
    f ∈ principalSeriesSpace F n χ ↔
      (∀ p : blockUpper F n (id : Fin n → Fin n), ∀ g, f (p * g) = borelChar χ p * f g) ∧
        ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
          ∀ k ∈ K, ∀ g, f (g * k) = f g := by
  rw [mem_parabolicIndSpace]
  simp only [charRep_apply, smul_eq_mul, borelChar_apply, mul_assoc]

theorem leviProj_mem_integralGL {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) :
    ((leviProj F n id p : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) ∈ integralGL F n := by
  rw [mem_integralGL_iff] at hp ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [leviProj_apply]
    split_ifs
    · exact hp.1 i j
    · exact (𝒪[F]).zero_mem
  · have : ((leviProj F n id p : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)⁻¹ =
        ((leviProj F n id p⁻¹ : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) := by
      rw [map_inv, Subgroup.coe_inv]
    rw [this, leviProj_apply]
    split_ifs
    · exact hp.2 i j
    · exact (𝒪[F]).zero_mem

variable {χ : levi F n (id : Fin n → Fin n) →* ℂ}

theorem borelChar_eq_one (hχ : IsUnramified χ) {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : borelChar χ p = 1 := by
  rw [borelChar_apply, hχ _ (leviProj_mem_integralGL hp), mul_one]
  show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1
  rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
  simp

theorem borelChar_eq_of_mul_eq (hχ : IsUnramified χ) {b b' : blockUpper F n (id : Fin n → Fin n)}
    {k k' : GL (Fin n) F} (hk : k ∈ integralGL F n) (hk' : k' ∈ integralGL F n)
    (h : (b : GL (Fin n) F) * k = b' * k') : borelChar χ b = borelChar χ b' := by
  have hm : ((b'⁻¹ * b : blockUpper F n (id : Fin n → Fin n)) : GL (Fin n) F) ∈ integralGL F n := by
    have : ((b'⁻¹ * b : blockUpper F n (id : Fin n → Fin n)) : GL (Fin n) F) = k' * k⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h,
        mul_inv_cancel_right]
    rw [this]
    exact mul_mem hk' (inv_mem hk)
  have := borelChar_eq_one hχ hm
  rw [map_mul, map_inv] at this
  have hne : borelChar χ b' ≠ 0 := by
    intro h0
    have h1 : borelChar χ (b'⁻¹ * b') = 1 := by rw [inv_mul_cancel, map_one]
    rw [map_mul, h0, mul_zero] at h1
    exact zero_ne_one h1
  calc borelChar χ b = borelChar χ b' * ((borelChar χ b')⁻¹ * borelChar χ b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = borelChar χ b' := by rw [this, mul_one]

theorem exists_borel_mul (g : GL (Fin n) F) :
    ∃ p : blockUpper F n (id : Fin n → Fin n), ∃ k ∈ integralGL F n, g = (p : GL (Fin n) F) * k := by
  obtain ⟨p, hp, k, hk, h⟩ := exists_blockUpper_mul_integralGL F n (β := (id : Fin n → Fin n))
    monotone_id g
  exact ⟨⟨p, hp⟩, k, hk, h⟩

variable (χ) in

def sphericalFun (g : GL (Fin n) F) : ℂ :=
  borelChar χ (exists_borel_mul g).choose

theorem sphericalFun_mul (hχ : IsUnramified χ) (b : blockUpper F n (id : Fin n → Fin n))
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    sphericalFun χ ((b : GL (Fin n) F) * k) = borelChar χ b := by
  obtain ⟨k', hk', h⟩ := (exists_borel_mul ((b : GL (Fin n) F) * k)).choose_spec
  exact borelChar_eq_of_mul_eq hχ hk' hk h.symm

theorem sphericalFun_borel (hχ : IsUnramified χ) (b : blockUpper F n (id : Fin n → Fin n)) :
    sphericalFun χ (b : GL (Fin n) F) = borelChar χ b := by
  simpa using sphericalFun_mul hχ b (integralGL F n).one_mem

theorem sphericalFun_one (hχ : IsUnramified χ) : sphericalFun χ 1 = 1 := by
  simpa using sphericalFun_borel hχ 1

theorem sphericalFun_mem (hχ : IsUnramified χ) : sphericalFun χ ∈ principalSeriesSpace F n χ := by
  rw [mem_principalSeriesSpace]
  refine ⟨fun p g => ?_, integralGL F n, isOpen_integralGL F n, fun k hk g => ?_⟩
  · obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
    rw [← mul_assoc, ← Subgroup.coe_mul, sphericalFun_mul hχ _ hk, sphericalFun_mul hχ _ hk,
      map_mul]
  · obtain ⟨b, k', hk', rfl⟩ := exists_borel_mul g
    rw [mul_assoc, sphericalFun_mul hχ _ (mul_mem hk' hk), sphericalFun_mul hχ _ hk']

def sphericalVector (hχ : IsUnramified χ) : principalSeriesSpace F n χ :=
  ⟨sphericalFun χ, sphericalFun_mem hχ⟩

@[simp]
theorem coe_sphericalVector (hχ : IsUnramified χ) :
    ((sphericalVector hχ : principalSeriesSpace F n χ) : GL (Fin n) F → ℂ) = sphericalFun χ := rfl

theorem sphericalVector_mem_fixedVectors (hχ : IsUnramified χ) :
    sphericalVector hχ ∈ fixedVectors (principalSeries F n χ) (integralGL F n) := by
  intro k hk
  refine Subtype.ext (funext fun g => ?_)
  rw [coe_indRep_apply]
  obtain ⟨b, k', hk', rfl⟩ := exists_borel_mul g
  simp only [coe_sphericalVector]
  rw [mul_assoc, sphericalFun_mul hχ _ (mul_mem hk' hk), sphericalFun_mul hχ _ hk']

theorem sphericalVector_ne_zero (hχ : IsUnramified χ) : sphericalVector hχ ≠ 0 := by
  intro h
  have := congrFun (congrArg Subtype.val h) 1
  simp only [coe_sphericalVector, Submodule.coe_zero, Pi.zero_apply] at this
  rw [sphericalFun_one hχ] at this
  exact one_ne_zero this

theorem eq_smul_sphericalVector (hχ : IsUnramified χ) {f : principalSeriesSpace F n χ}
    (hf : f ∈ fixedVectors (principalSeries F n χ) (integralGL F n)) :
    f = (f : GL (Fin n) F → ℂ) 1 • sphericalVector hχ := by
  have hmem := (mem_principalSeriesSpace.1 f.2).1
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
  have hfk : (f : GL (Fin n) F → ℂ) ((b : GL (Fin n) F) * k) = (f : GL (Fin n) F → ℂ) b := by
    have := congrFun (congrArg Subtype.val (hf k hk)) (b : GL (Fin n) F)
    rw [coe_indRep_apply] at this
    exact this
  rw [Submodule.coe_smul, Pi.smul_apply, coe_sphericalVector, sphericalFun_mul hχ _ hk, hfk,
    smul_eq_mul]
  have := hmem b 1
  rw [mul_one] at this
  rw [this, mul_comm]

theorem fixedVectors_eq_span (hχ : IsUnramified χ) :
    fixedVectors (principalSeries F n χ) (integralGL F n) = ℂ ∙ sphericalVector hχ := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    exact ⟨_, (eq_smul_sphericalVector hχ hf).symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact sphericalVector_mem_fixedVectors hχ

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

variable (μ) in

abbrev SphericalHecke : Type _ :=
  HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n) (isOpen_integralGL F n)

variable (μ χ) in

def sphericalEigen (h : SphericalHecke μ (F := F) (n := n)) : ℂ :=
  ∫ g, (h : HeckeAlgebra μ) g * sphericalFun χ g ∂μ

theorem heckeAct_sphericalVector (hχ : IsUnramified χ) (h : SphericalHecke μ (F := F) (n := n)) :
    heckeAct μ (principalSeries F n χ) (h : HeckeAlgebra μ) (sphericalVector hχ) =
      sphericalEigen χ μ h • sphericalVector hχ := by
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep χ)
  have hmem : heckeAct μ (principalSeries F n χ) (h : HeckeAlgebra μ) (sphericalVector hχ) ∈
      fixedVectors (principalSeries F n χ) (integralGL F n) :=
    heckeAct_mem_fixedVectors (h : HeckeAlgebra μ).mem
      (fun _ hk x => HeckeAlgebraLevel.apply_mul_left _ _ h hk x) (hs _)
  rw [eq_smul_sphericalVector hχ hmem]
  congr 1
  have := dual_heckeAct μ (h : HeckeAlgebra μ).mem (hs (sphericalVector hχ))
    (evalOne (blockUpper F n (id : Fin n → Fin n)) (inflateTwist F n id (charRep χ)))
  simp only [evalOne_apply, coe_indRep_apply, one_mul, coe_sphericalVector] at this
  exact this

variable (μ) in

def sphericalCharacter (hχ : IsUnramified χ) : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] ℂ :=
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep χ)
  have hne := sphericalVector_ne_zero hχ
  have key : ∀ a b : ℂ, a • sphericalVector hχ = b • sphericalVector hχ → a = b :=
    fun a b hab => smul_left_injective ℂ hne hab
  { toFun := sphericalEigen χ μ
    map_one' := key _ _ (by
      rw [← heckeAct_sphericalVector, one_smul, HeckeAlgebraLevel.val_one]
      exact heckeAct_idem_of_mem _ _ (sphericalVector_mem_fixedVectors hχ))
    map_mul' := fun a b => key _ _ (by
      rw [← heckeAct_sphericalVector, HeckeAlgebraLevel.val_mul, heckeAct_mul _ _ (hs _),
        heckeAct_sphericalVector, heckeAct_smul_right (a : HeckeAlgebra μ).mem _ (hs _),
        heckeAct_sphericalVector, smul_smul, mul_comm])
    map_zero' := key _ _ (by
      rw [← heckeAct_sphericalVector, HeckeAlgebraLevel.val_zero, coe_zero, zero_smul]
      exact heckeAct_zero_left (hs _))
    map_add' := fun a b => key _ _ (by
      rw [← heckeAct_sphericalVector, HeckeAlgebraLevel.val_add, coe_add,
        heckeAct_add_left (a : HeckeAlgebra μ).mem (b : HeckeAlgebra μ).mem (hs _),
        heckeAct_sphericalVector, heckeAct_sphericalVector, add_smul])
    commutes' := fun c => key _ _ (by
      rw [← heckeAct_sphericalVector, Algebra.algebraMap_eq_smul_one, HeckeAlgebraLevel.val_smul,
        HeckeAlgebra.coe_smul, heckeAct_smul_left c (HeckeAlgebra.mem _) (hs _), HeckeAlgebraLevel.val_one,
        heckeAct_idem_of_mem _ _ (sphericalVector_mem_fixedVectors hχ)]
      rfl) }

theorem sphericalCharacter_apply (hχ : IsUnramified χ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ hχ h = sphericalEigen χ μ h := rfl

end Spherical

end GroundTheory.Automorphic

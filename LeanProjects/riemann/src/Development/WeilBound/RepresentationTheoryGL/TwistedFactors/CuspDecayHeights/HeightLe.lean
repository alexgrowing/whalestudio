import Mathlib
import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.HarishChandraCentre

noncomputable section

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm
open scoped ENNReal NumberField.AdeleRing

namespace PositivityTheory.Rg.Tf.Core

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

abbrev G1 : Type _ := normOneGL K n

abbrev Gam : Subgroup (G1 K n) := rationalGLOne K n

abbrev CC : Type _ := CompactlySupportedContinuousMap (G1 K n) ℂ

variable {K n}

abbrev L2 (μ : Measure (G1 K n)) : Type _ := Lp ℂ 2 (quotientMeasure (Gam K n) μ)

variable (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

def Rop (f : CC K n) : L2 μ →L[ℂ] L2 μ :=
  (rightRegularRep (Gam K n) μ).integrated μ (UnitaryRep.ccToL1 μ f)

def Pc : L2 μ →L[ℂ] L2 μ := (CuspidalSpectrum.cuspidalL2 μ).starProjection

variable {μ}

variable (μ) in

structure Twist where
  e : G1 K n ≃ₜ* G1 K n
  mem_gam : ∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n
  pres : MeasurePreserving e μ μ
  height_le : ∃ C : ℝ, ∃ c : ℕ, ∀ g : G1 K n,
    AutomorphicForm.height ((e g : G1 K n) : AdelicGLn.AdelicGL K n) ≤ C * AutomorphicForm.height (g : AdelicGLn.AdelicGL K n) ^ c
  U : L2 μ →L[ℂ] L2 μ
  U_spec : ∀ φ : L2 μ, (U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
    fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y)))

  U_comm : U ∘L Pc μ = Pc μ ∘L U

def Twist.id (μ : Measure (G1 K n)) [μ.IsHaarMeasure] : Twist μ where
  e := ContinuousMulEquiv.refl _
  mem_gam _ := Iff.rfl
  pres := MeasurePreserving.id μ
  height_le := ⟨1, 1, fun g => by simp⟩
  U := ContinuousLinearMap.id ℂ _
  U_spec φ := by
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [ContinuousLinearMap.id_apply]
    congr 1
    exact (Quotient.out_eq y).symm
  U_comm := by simp

def twK (θ : Twist μ) (f : CC K n) (x : G1 K n) : ℂ :=
  ∑ᶠ γ : Gam K n, f (x⁻¹ * (γ : G1 K n) * θ.e x)

def twKQ (θ : Twist μ) (f : CC K n) (y : RightCosetSpace (Gam K n)) : ℂ :=
  twK θ f (Quotient.out y)

def twInt (θ : Twist μ) (f : CC K n) : ℂ :=
  ∫ y, twKQ θ f y ∂quotientMeasure (Gam K n) μ

def qht (x : G1 K n) : ℝ :=
  ⨅ γ : Gam K n, AutomorphicForm.height (((γ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)

variable (μ) in

def cuspTr (θ : Twist μ) (f : CC K n) : ℂ :=
  trace (Pc μ ∘L Rop μ f ∘L θ.U ∘L Pc μ)

end PositivityTheory.Rg.Tf.Core

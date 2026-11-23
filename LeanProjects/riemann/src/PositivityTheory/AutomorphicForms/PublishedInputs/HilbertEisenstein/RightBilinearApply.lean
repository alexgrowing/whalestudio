import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PolyVHasTemperateGrowth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

abbrev Vr (F : Type) [Field F] [NumberField F] : Type := Fin 2 → UpperTheory.V.TR.Rinf F

def Xi (F : Type) [Field F] : Type := {ξ : Fin 2 → F // ξ ≠ 0}

instance : MeasurableSpace (Xi F) := ⊤

instance : MeasurableSingletonClass (Xi F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

instance : Countable (Xi F) := inferInstanceAs (Countable {ξ : Fin 2 → F // ξ ≠ 0})

abbrev Pp (F : Type) [Field F] [NumberField F] : Type := {r : ℝ // 0 < r} × normOneSubgroup F

def av (p : Pp F) : Ideles F := moduleSection (w0 F) p.1 * (p.2 : Ideles F)

def μS (F : Type) [Field F] [NumberField F] (S : Set {r : ℝ // 0 < r}) : Measure (Pp F × Xi F) :=
  ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))).prod
    Measure.count

def Mrow (g : GA F 2) (a : Ideles F) : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) a * g

def Mcol (g : GA F 2) (a : Ideles F) : GA F 2 := g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹

def rowv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) : Fin 2 → Ad F :=
  rowA ξ ᵥ* ((Mrow g a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))

def colv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) : Fin 2 → Ad F :=
  ((Mcol g a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ

open Classical in

def finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

open Classical in

def finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)
  then ((finiteAdelicChar F (pFin F (y 1)) : Circle) : ℂ) else 0

def vInf (y : Fin 2 → Ad F) : Vr F := fun i => UpperTheory.V.TR.pInf F (y i)

def kap1 (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (q : Pp F × Xi F) : ℂ :=
  finRow c (rowv g (av q.1) q.2.1) * ((χ.1 (av q.1) : ℂˣ) : ℂ)⁻¹ * ((q.1.1 : ℝ) : ℂ)

def w1 (g : GA F 2) (q : Pp F × Xi F) : Vr F := vInf (rowv g (av q.1) q.2.1)

def kap2 (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (q : Pp F × Xi F) : ℂ :=
  finCol c (colv g (av q.1) q.2.1) * ((χ.1 (av q.1) : ℂˣ) : ℂ)⁻¹ * ((q.1.1 : ℝ) : ℂ)⁻¹

def w2 (g : GA F 2) (q : Pp F × Xi F) : Vr F := vInf (colv g (av q.1) q.2.1)

def B1lin : Vr F →ₗ[ℝ] UpperTheory.V.TR.Lie F 2 →ₗ[ℝ] Vr F :=
  LinearMap.mk₂ ℝ (fun w x => w ᵥ* Matrix.of x)
    (fun w w' x => Matrix.add_vecMul _ _ _) (fun r w x => Matrix.smul_vecMul _ _ _)
    (fun w x x' => by exact Matrix.vecMul_add _ _ _)
    (fun r w x => by exact Matrix.vecMul_smul (R := ℝ) _ _ _)

def B2lin : Vr F →ₗ[ℝ] UpperTheory.V.TR.Lie F 2 →ₗ[ℝ] Vr F :=
  LinearMap.mk₂ ℝ (fun w z => Matrix.of z *ᵥ w)
    (fun w w' z => Matrix.mulVec_add _ _ _) (fun r w z => Matrix.mulVec_smul _ _ _)
    (fun w z z' => by exact Matrix.add_mulVec _ _ _)
    (fun r w z => by exact Matrix.smul_mulVec (R := ℝ) _ _ _)

def B1 : Vr F →L[ℝ] UpperTheory.V.TR.Lie F 2 →L[ℝ] Vr F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B1lin)

def B2 : Vr F →L[ℝ] UpperTheory.V.TR.Lie F 2 →L[ℝ] Vr F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B2lin)

@[simp] theorem left_bilinear_apply (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : B1 w x = w ᵥ* Matrix.of x := rfl

@[simp] theorem right_bilinear_apply (w : Vr F) (z : UpperTheory.V.TR.Lie F 2) : B2 w z = Matrix.of z *ᵥ w := rfl

def invL (x : UpperTheory.V.TR.Lie F 2) : UpperTheory.V.TR.Lie F 2 := UpperTheory.V.TR.toL (Matrix.of x)⁻¹

def dl (g : GA F 2) (x : UpperTheory.V.TR.Lie F 2) : ℝ := absD g * ∏ v, (Matrix.det (Matrix.of x)) v

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

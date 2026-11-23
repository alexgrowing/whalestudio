import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

variable {K : Type} [Field K] [NumberField K]

def omW {c : HeckeCharacter K} {v : Pl} : LM c v → (Qv v)ˣ → ℂ
  | LM.sp w₁ w₂ _ => fun a => ((cAt c v w₁ a * cAt c v w₂ a : ℂˣ) : ℂ)
  | LM.ns w _ η _ => fun a => (((GL2LocalData.resF (F := Qv v) (localChar c w) * η) a : ℂˣ) : ℂ)

def om0 {c : HeckeCharacter K} {v : Pl} : LM c v → (Qv v)ˣ → ℂ
  | LM.sp w₁ _ _ => fun a => ((cAt c v w₁ a * cAt c v w₁ a : ℂˣ) : ℂ)
  | LM.ns w _ η _ => fun a => (((GL2LocalData.resF (F := Qv v) (localChar c w) * η) a : ℂˣ) : ℂ)

def omR (n : ℤ) (t : ℝ) (a : ℝˣ) : ℂ :=
  chC n (Complex.I * t) (Units.mk0 ((|(a : ℝ)| : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr a.ne_zero))) * sgR a *
    (if 0 < (a : ℝ) then 1 else (-1 : ℂ) ^ n)

def uW {c : HeckeCharacter K} (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (z : Jd) : ℂ :=
  omR n t (RationalIdeles.realPart z) * ∏ᶠ v, omW (M v) (Ad3.R.lc v z)

def u0 {c : HeckeCharacter K} (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (z : Jd) : ℂ :=
  omR n t (RationalIdeles.realPart z) * ∏ᶠ v, om0 (M v) (Ad3.R.lc v z)

end GlobalTheory.CompanionTheory.CenTheta

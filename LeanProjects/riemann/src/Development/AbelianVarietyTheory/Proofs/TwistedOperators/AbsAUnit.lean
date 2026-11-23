import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped TensorProduct NNReal

namespace GlobalTheory.LeviShift

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (Φ : WittFrame V)

def bas (u : SV (wittIndex V)) (i : Fin (wittIndex V)) : V.V := if u i = -1 then Φ.f i else Φ.e i

def dbas (u : SV (wittIndex V)) (i : Fin (wittIndex V)) : V.V := if u i = -1 then Φ.e i else Φ.f i

abbrev Supp {k : ℕ} (u : SV k) : Type := {i : Fin k // u i ≠ 0}

variable (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

def detMat (u : SV (wittIndex V)) (g : HA R hc.sig V.gram) : Matrix (Supp u) (Supp u) (R ⊗[F] E) :=
  Matrix.of fun i j => hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u j)))
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u i))

def detU (u : SV (wittIndex V)) (g : HA R hc.sig V.gram) : R ⊗[F] E := (detMat Φ hc R u g).det

end General

def absA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : AF F ⊗[F] E) : ℝ≥0 :=
  open Classical in if h : IsUnit z then Doubling.absE F E h.unit else 0

theorem absA_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z w : AF F ⊗[F] E) :
    absA F E (z * w) = absA F E z * absA F E w := by
  classical
  unfold absA
  by_cases hz : IsUnit z <;> by_cases hw : IsUnit w
  · rw [dif_pos (hz.mul hw), dif_pos hz, dif_pos hw, ← map_mul]; congr 1; ext; rfl
  · rw [dif_neg (fun h => hw (isUnit_of_mul_isUnit_right h)), dif_neg hw, mul_zero]
  · rw [dif_neg (fun h => hz (isUnit_of_mul_isUnit_left h)), dif_neg hz, zero_mul]
  · rw [dif_neg (fun h => hz (isUnit_of_mul_isUnit_left h)), dif_neg hz, zero_mul]

theorem absA_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : (AF F ⊗[F] E)ˣ) :
    absA F E z = Doubling.absE F E z := by
  classical
  rw [absA, dif_pos z.isUnit]; rfl

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

def logDelta (u : SV (wittIndex V)) (g : GA D V) : ℝ :=
  Real.log (absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) u g))

end GlobalTheory.LeviShift

end

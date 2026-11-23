import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.PureTh

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def TPURE : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (S0 : Finset Pl), (∀ v ∈ S0, PureTh c v (Wtf v)) →
  (∀ v ∉ S0, Unr c v ∧ StdTh c v (Wtf v)) → ∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 (thR n t) Wtf)

open Classical in

def TLIN : Prop := ∀ (Wi : GL (Fin 2) ℝ → ℂ) (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ), SphAE Wtf →
  ∀ (v₀ : Pl) (W₁ W₂ : GL (Fin 2) (Qv v₀) → ℂ),
  (∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 Wi (Function.update Wtf v₀ W₁))) →
  (∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 Wi (Function.update Wtf v₀ W₂))) →
  ∀ a b : ℂ, ∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 Wi (Function.update Wtf v₀ (a • W₁ + b • W₂)))

open Classical in

def TZERO : Prop := ∀ (Wi : GL (Fin 2) ℝ → ℂ) (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ), SphAE Wtf →
  ∀ v₀ : Pl, ∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 Wi (Function.update Wtf v₀ 0))

def MODRT : Prop := ∀ (θ : G2 → ℂ) (h : G2), ModG θ → ModG (fun g => θ (g * h))

def GAURT : Prop := ∀ (Wt : G2 → ℂ) (h : G2), (∀ (x : 𝔸[ℚ]) g, Wt (uni2 x * g) = (adelicChar ℚ (-x) : ℂ) * Wt g) →
  Gau2 Wt → Gau2 (fun g => Wt (g * h))

def TTRANS : Prop := ∀ (θ Cst Wt : G2 → ℂ) (h : G2), ThX θ Cst Wt →
  ThX (fun g => θ (g * h)) (fun g => Cst (g * h)) (fun g => Wt (g * h))

def LOCEX : Prop := ∀ (v : Pl) (x : GL (Fin 2) (Qv v)), ∃ h : G2, IsLoc2 v x h

open Classical in

def PWT : Prop := ∀ (v₀ : Pl) (x : GL (Fin 2) (Qv v₀)) (h : G2), IsLoc2 v₀ x h →
  ∀ (Wi : GL (Fin 2) ℝ → ℂ) (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (W : GL (Fin 2) (Qv v₀) → ℂ) (g : G2),
    pw2 Wi (Function.update Wtf v₀ (fun y => W (y * x))) g = pw2 Wi (Function.update Wtf v₀ W) (g * h)

variable (K) in

def ENL : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (S : Finset (PlK K)),
  (∀ w ∉ S, IsUnramifiedChar (localChar c w)) → ∃ S1 : Finset Pl, ∀ v ∉ S1, Unr c v

variable (K) in

def ASM : Prop := STDSPH K → TPURE K → TLIN → TZERO → TTRANS → LOCEX → PWT → THETAB K

end Ad3.K.QuadraticBaseChangeGL3.Th

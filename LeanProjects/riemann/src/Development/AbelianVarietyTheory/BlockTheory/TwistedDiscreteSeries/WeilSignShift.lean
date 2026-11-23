import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NcGapGt (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h < |((x.1 - y.1 : ℚ) : ℝ)|

def NcGapGe (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |((x.1 - y.1 : ℚ) : ℝ)|

def minSig (S : SPar) : ℕ :=
  min (S.filter fun x => x.2 = true).card (S.filter fun x => x.2 = false).card

def shiftPar (c : ℚ) (S : SPar) : SPar := S.image fun x => (x.1 + c, x.2)

variable (D : D7)

def alV (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i - 1 / 2 else -(D.hc τ).e i

def alW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i else -(D.hc τ).e i - 1 / 2

def lamS (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alW D i τ) (parA (Ptw D) i τ)

def lamT (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alV D i τ) (parA (Ptw D) ((i : ℕ) + 1) τ)

def StepGap (i : Fin D.R.m) : Prop :=
  ∀ τ, NcGapGt (lamS D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGt (lamT D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGe (lamS D i τ) (120 * (D.R.rankY i : ℝ) * (minSig (lamS D i τ) : ℝ) ^ ((3 : ℝ) / 2))

variable {D}

def StepWeil (ψ : AddChar (AF D.host.F) ℂ) (i : Fin D.R.m) (V W : HSp D)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop :=
  ∃ χV χW : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χV χW ω ∧
    ∀ τ, HasInfExp D χV τ (alV D i τ) ∧ HasInfExp D χW τ (alW D i τ)

def VacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f

def fockOf {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f

def ItPair (D : D7) : Prop :=
  ∀ (i : Fin D.R.m), StepGap D i →
    ∀ (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar), S = parB (Ptw D) i → S' = parB (Ptw D) ((i : ℕ) + 1) →
    ∀ (M : DSModel V S) (M' : DSModel W S'),
      ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
        ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ),
          StepWeil ψ i V W ω → VacVec ψ θ M M' f → f ≠ 0 →
            IsItW θ M M' ω (fockOf ψ θ M M' f) It

end GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

end

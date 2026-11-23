import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge

noncomputable section

namespace PI.AdBridgeSteps

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def IsFormula (I : AutInst) (f : HAd I → I.GA) : Prop :=
  ∀ h, (∀ v, uMat ((f h).1 v) = ofHAInf I h v) ∧ I.fmat (f h).2 = ofHAFin I h

def InvAlg : Prop :=
  ∀ I : AutInst, ∃ f : HAd I →* I.GA, IsFormula I f ∧ Function.Bijective f

def InvTop : Prop :=
  ∀ (I : AutInst) (f : HAd I → I.GA), IsFormula I f → Continuous f ∧ IsOpenMap f

def RealK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε k →
    (kᴴ * k = 1 ↔ ∀ a b, ε a ≠ ε b → k a b = 0)

def FinK : Prop :=
  ∀ (I : AutInst) (h : HAd I),
    (∀ x, x ∈ I.Lf ↔ ofHAFin I h *ᵥ x ∈ I.Lf) ↔
      ∀ v : HeightOneSpectrum (𝓞 I.F),
        Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) ∈
          Formalism.L2.SG.Sub.Kloc v (I.L : Set (Fin I.n → I.E))

end PI.AdBridgeSteps

import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.IsLowPairZero
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDualParamAt {S : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (τ : D.what₂.Tau) (α : ℚ) {r s : ℕ}
    (lam' : Ix r s → ℚ) : Prop :=
  ∃ e : Fin S.rank ≃ Ix r s, ∀ a, (M.ε τ a = true ↔ (e a).isLeft = true) ∧ M.lam τ a = (α : ℝ) + (lam' (e a) : ℝ)

open Classical in

def ARvO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T' : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (χS χT : (AE D)ˣ →* Circle)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
    Formalism.IndefR.Fock.Sk.PairSetup ψ θ S T' sS sT BS BT pS pT → IsWeilDatumO ψ S T' χS χT om' →
    ∀ (τ : D.what₂.Tau) (αT : ℚ), HasInfExp D χT τ αT →
    ∀ {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (t i : ℕ) (al be ga de : List ℚ),
      ((HypA t al be ga de ∧ HypG t al be ga de ∧ IsDualParamAt M τ αT (lamA' t al be ga de)) ∨
        (HypA t al be ga de ∧ HypGm t al be ga de ∧ IsDualParamAt M τ αT (lamM' t al be ga de))) →
      1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → T'.SigOK →
      T'.sig (tauE D τ) = (al.length + be.length - i, ga.length + de.length - i) →
      (¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) →
      ∀ f₀ : WO S T' → ℂ, IsThetaFunO ψ S T' f₀ →
        (∀ τ', IsFockVacAt (heisO ψ S T') θ τ' (cplxO (sS τ') (sT τ')) f₀) →
      ∀ B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ),
        IsLowPair θ M om' (pureTensorO ψ θ S T' sS sT BS BT f₀) B →
        (∀ v, IsLinearMap ℂ (fun φ => B φ v)) →
        (∀ φ τ' (v : M.Vec) (w w' : M.sm τ') (c : ℂ),
          B φ (Function.update v τ' (c • w + w')) = c • B φ (Function.update v τ' w) + B φ (Function.update v τ' w')) →
        (∀ φ τ' (v : M.Vec) (g' : GA D T'), ∃ ℓ : M.H τ' →ₗ[ℂ] ℂ, Sobolev₂ (lieAt S τ') (M.rep τ') ℓ ∧
          ∀ w : M.sm τ', ℓ w = B φ (Function.update v τ' w) g') →
        B = 0

end Formalism.IndefR.Tow

end

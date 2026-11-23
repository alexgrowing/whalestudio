import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.IsDualParamAt
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def KAt {k : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.UH G ∧ g * s = s * g}

def KFinAt {S : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (τ : D.what₂.Tau)
    (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (w : M.H τ) : Prop :=
  ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ w ∈ W ∧
    ∀ g ∈ KAt (gramAt D S τ) s, ∀ x ∈ W, M.rep τ g x ∈ W

def ParamOfData : Prop :=
  ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de →
    IsParam (lamA' t al be ga de) ∧ IsParam (lamM' t al be ga de)

def SobKFinDenseO (D : D7) : Prop :=
  ∀ {S : HSp D} {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ),
    IsCartanInv (gramAt D S τ) s → ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt S τ) (M.rep τ) ℓ →
      (∀ w : M.sm τ, KFinAt M τ s (w : M.H τ) → ℓ w = 0) → ∀ w : M.sm τ, ℓ w = 0

def DSTiesSq (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → ∃ e ε lamS c σ χ E, Formalism.MainNotions.J.DSTieAt X p q lam e ε lamS c σ χ E ∧
    ∃ m : ℤ, (m : ℝ) = 2 * c ∧ ∀ g, χ g = (((X.grp p q).sq g : ℂˣ) : ℂ) ^ (-m)

open Classical in

def GlobalThetaOrthogonality (D : D7) : Prop :=
  ∀ X : ProvA, Formalism.MainNotions.SchurIrreducible.AdmA X → ProvisionCompatibility D X → DSTiesSq X →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T' : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (χS χT : (AE D)ˣ →* Circle)
    (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
    Formalism.IndefR.Fock.Sk.PairSetup ψ θ S T' sS sT BS BT pS pT → IsWeilDatumO ψ S T' χS χT om' →
    ∀ (τ : D.what₂.Tau) (αT : ℚ), HasInfExp D χT τ αT →
    ∀ {Ss : D.what₂.Tau → SPar} (M : DSModel S Ss) {p q r s : ℕ} (lam' : Ix r s → ℚ),
      IsParam lam' → GapGt lam' (((r + s : ℕ) : ℝ) ^ 3) → IsDualParamAt M τ αT lam' → T'.SigOK →
      T'.sig (tauE D τ) = (p, q) →
      ∀ f₀ : WO S T' → ℂ, IsThetaFunO ψ S T' f₀ →
        (∀ τ', IsFockVacAt (heisO ψ S T') θ τ' (cplxO (sS τ') (sT τ')) f₀) →
      ∀ B : MvPolynomial (FVar D T'.rank S.rank) ℂ → M.Vec → (GA D T' → ℂ),
        IsLowPair θ M om' (pureTensorO ψ θ S T' sS sT BS BT f₀) B →
        (∀ v, IsLinearMap ℂ (fun φ => B φ v)) →
        (∀ φ τ' (v : M.Vec) (w w' : M.sm τ') (c : ℂ),
          B φ (Function.update v τ' (c • w + w')) = c • B φ (Function.update v τ' w) + B φ (Function.update v τ' w')) →
        ∀ φ (v : M.Vec) (g' : GA D T'), KFinAt M τ (sS τ) (v τ : M.H τ) → B φ v g' ≠ 0 →
          ∃ (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
            IsIntw (X.fock p q r s) MM (X.ds r s lam').HK f ∧ f ≠ 0

open Classical in

def ArvOKF (D : D7) : Prop :=
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
        ∀ φ (v : M.Vec) (g' : GA D T'), KFinAt M τ (sS τ) (v τ : M.H τ) → B φ v g' = 0

def ProvAInstO (D : D7) : Prop := ∃ X : ProvA, Formalism.MainNotions.SchurIrreducible.AdmA X ∧ ProvisionCompatibility D X ∧ DSTiesSq X

end Formalism.IndefR.Tow

end

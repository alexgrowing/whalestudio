import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev RPt (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Fin m → Fin n → ℂ

def IsRealPtO (θ : InfFam D) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) : Prop :=
  w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of (z τ)

def realPt (θ : InfFam D) {m n : ℕ} (z : RPt D m n) : Mx D m n :=
  Classical.epsilon (IsRealPtO θ z)

def gramAt (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  V.gram.map (tauE D τ)

def efAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  -2 * (tauE D τ D.host.xi0 * ((gramAt S τ)⁻¹ * yᴴ * gramAt T τ * x).trace).re

def hAt (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  (efAt S T τ (cplxO (sS τ) (sT τ) x) y : ℂ) + Complex.I * (efAt S T τ x y : ℂ)

def hR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (z z' : RPt D T.rank S.rank) : ℂ :=
  ∑ τ, hAt S T sS sT τ (Matrix.of (z τ)) (Matrix.of (z' τ))

def xiO (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) : RPt D T.rank S.rank → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * ((hR S T sS sT z z).re : ℂ) / 2) * f (realPt θ z)

def ratInf (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : RPt D T.rank S.rank :=
  fun τ i j => tauE D τ (γ i j)

def jR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (z : RPt D T.rank S.rank) : RPt D T.rank S.rank :=
  fun τ => (cplxO (sS τ) (sT τ) (Matrix.of (z τ)) : Fin T.rank → Fin S.rank → ℂ)

def RealOk (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : Prop :=
  IsInfFam θ ∧ (∀ τ, IsCartanInv (gramAt S τ) (sS τ)) ∧ ∀ τ, IsCartanInv (gramAt T τ) (sT τ)

def RealPtEx (D : D7) : Prop :=
  ∀ (θ : InfFam D) (m n : ℕ), IsInfFam θ → ∀ z : RPt D m n, ∃! w, IsRealPtO θ z w

def XiHeis (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → RealOk θ S T sS sT →
    ∀ f, IsThetaFunO ψ S T f → ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : RPt D T.rank S.rank),
      xiO θ S T sS sT (heisO ψ S T (ratW T S γ - realPt θ (ratInf S T γ)) f) z =
        Complex.exp ((Real.pi : ℂ) * hR S T sS sT z (ratInf S T γ) -
            (Real.pi : ℂ) * hR S T sS sT (ratInf S T γ) (ratInf S T γ) / 2) *
          xiO θ S T sS sT f (z - ratInf S T γ)

def XiHol (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → RealOk θ S T sS sT →
    ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      ∀ z, DifferentiableAt ℝ (xiO θ S T sS sT f) z ∧
        ∀ v, fderiv ℝ (xiO θ S T sS sT f) z (jR S T sS sT v) = Complex.I * fderiv ℝ (xiO θ S T sS sT f) z v

def fockDir (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (k : FVar D T.rank S.rank) : RPt D T.rank S.rank :=
  open Classical in fun τ => if τ = k.1 then (unitMap (B k.1) (B' k.1) k.2.1 k.2.2 : Fin T.rank → Fin S.rank → ℂ) else 0

def jetR (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (G : RPt D T.rank S.rank → ℂ)
    (k : FVar D T.rank S.rank →₀ ℕ) : ℂ :=
  opPow (fun v (F : RPt D T.rank S.rank → ℂ) z => fderiv ℝ F z (fockDir S T B B' v)) k G 0

def XiJet (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), IsStdChar D ψ (-1) → RealOk θ S T sS sT →
    (∀ τ, IsONBasis (gramAt S τ) (sS τ) (B τ) (pS τ)) → (∀ τ, IsONBasis (gramAt T τ) (sT τ) (B' τ) (pT τ)) →
    ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      ∀ k : FVar D T.rank S.rank →₀ ℕ,
        fockVec (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' (MvPolynomial.monomial k 1) f 0 =
          (k.prod fun v e => (((Real.pi * (hR S T sS sT (fockDir S T B B' v) (fockDir S T B B' v)).re) : ℝ) : ℂ) ^
              (-(e : ℂ) / 2)) * jetR S T B B' (xiO θ S T sS sT f) k

end Formalism.IndefR.Mi

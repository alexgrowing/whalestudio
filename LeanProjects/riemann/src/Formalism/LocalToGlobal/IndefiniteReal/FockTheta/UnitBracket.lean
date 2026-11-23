import Formalism.LocalToGlobal.IndefiniteReal.DatumFock
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.FockPairGl
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

structure IsCCR {ι X : Type} [DecidableEq ι] (Sm : Set (X → ℂ)) (aP aM : ι → (X → ℂ) → (X → ℂ)) : Prop where
  zero_mem : (0 : X → ℂ) ∈ Sm
  add_mem : ∀ f g, f ∈ Sm → g ∈ Sm → f + g ∈ Sm
  smul_mem : ∀ (c : ℂ) f, f ∈ Sm → c • f ∈ Sm
  memP : ∀ i f, f ∈ Sm → aP i f ∈ Sm
  memM : ∀ i f, f ∈ Sm → aM i f ∈ Sm
  linP : ∀ i (c : ℂ) f g, f ∈ Sm → g ∈ Sm → aP i (f + c • g) = aP i f + c • aP i g
  linM : ∀ i (c : ℂ) f g, f ∈ Sm → g ∈ Sm → aM i (f + c • g) = aM i f + c • aM i g
  commP : ∀ i j f, f ∈ Sm → aP i (aP j f) = aP j (aP i f)
  ccr : ∀ i j f, f ∈ Sm → aM i (aP j f) - aP j (aM i f) = if i = j then f else 0

def CCRDerivAbs : Prop :=
  ∀ {ι X : Type} [DecidableEq ι] (Sm : Set (X → ℂ)) (aP aM : ι → (X → ℂ) → (X → ℂ)) (v : X → ℂ),
    IsCCR Sm aP aM → v ∈ Sm → (∀ i, aM i v = 0) →
      ∀ i (P : MvPolynomial ι ℂ), aM i (pureTensorL aP v P) = pureTensorL aP v (MvPolynomial.pderiv i P)

def CCRDerivAt : Prop :=
  ∀ {ι X : Type} [DecidableEq ι] (Sm : Set (X → ℂ)) (aP aM : ι → (X → ℂ) → (X → ℂ)) (v : X → ℂ),
    IsCCR Sm aP aM → v ∈ Sm → ∀ i, aM i v = 0 →
      ∀ P : MvPolynomial ι ℂ, aM i (pureTensorL aP v P) = pureTensorL aP v (MvPolynomial.pderiv i P)

def CCRMemAbs : Prop :=
  ∀ {ι X : Type} [DecidableEq ι] (Sm : Set (X → ℂ)) (aP aM : ι → (X → ℂ) → (X → ℂ)) (v : X → ℂ),
    IsCCR Sm aP aM → v ∈ Sm → ∀ P : MvPolynomial ι ℂ, pureTensorL aP v P ∈ Sm

def IsSesq {X : Type} (Sm : Set (X → ℂ)) (ip : (X → ℂ) → (X → ℂ) → ℂ) : Prop :=
  ∀ f g h (c : ℂ), f ∈ Sm → g ∈ Sm → h ∈ Sm →
    ip (f + c • g) h = ip f h + c * ip g h ∧ ip h (f + c • g) = ip h f + starRingEnd ℂ c * ip h g

def FockNormAbs : Prop :=
  ∀ {ι X : Type} [DecidableEq ι] (Sm : Set (X → ℂ)) (aP aM : ι → (X → ℂ) → (X → ℂ)) (v : X → ℂ)
    (ip : (X → ℂ) → (X → ℂ) → ℂ),
    IsCCR Sm aP aM → v ∈ Sm → (∀ i, aM i v = 0) → IsSesq Sm ip →
    (∀ i f g, f ∈ Sm → g ∈ Sm → ip (aM i f) g = ip f (aP i g)) →
    (∀ i f g, f ∈ Sm → g ∈ Sm → ip (aP i f) g = ip f (aM i g)) →
      ∀ P Q : MvPolynomial ι ℂ, ip (pureTensorL aP v P) (pureTensorL aP v Q) = Formalism.REAL.fockF P Q * ip v v

variable {m n : ℕ}

def eM (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  2 * (ξ * (GS⁻¹ * wᴴ * GT * z).trace).re

def brk (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ) (sS : Matrix (Fin n) (Fin n) ℂ)
    (sT : Matrix (Fin m) (Fin m) ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  (eM GS GT ξ z w : ℂ) - Complex.I * (eM GS GT ξ z (cplxO sS sT w) : ℂ) +
    Complex.I * (eM GS GT ξ (cplxO sS sT z) w : ℂ) + (eM GS GT ξ (cplxO sS sT z) (cplxO sS sT w) : ℂ)

def brkPP (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ) (sS : Matrix (Fin n) (Fin n) ℂ)
    (sT : Matrix (Fin m) (Fin m) ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  (eM GS GT ξ z w : ℂ) - Complex.I * (eM GS GT ξ z (cplxO sS sT w) : ℂ) -
    Complex.I * (eM GS GT ξ (cplxO sS sT z) w : ℂ) - (eM GS GT ξ (cplxO sS sT z) (cplxO sS sT w) : ℂ)

def PosF (pS pT : ℕ) (i : Fin m) (c : Fin n) : Prop := ((i : ℕ) < pT ↔ (c : ℕ) < pS)

instance (pS pT : ℕ) (i : Fin m) (c : Fin n) : Decidable (PosF pS pT i c) := by unfold PosF; infer_instance

def UnitBracket : Prop :=
  ∀ (m n pS pT : ℕ) (GS sS BS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ),
    IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → ξ.re = 0 → 0 < ξ.im →
    (∀ i c, cplxO sS sT (unitMap BS BT i c) = (if PosF pS pT i c then Complex.I else -Complex.I) • unitMap BS BT i c) ∧
    (∀ i c i' c', brk GS GT ξ sS sT (unitMap BS BT i c) (unitMap BS BT i' c') =
      if i = i' ∧ c = c' then -(4 * ξ.im : ℂ) * Complex.I else 0) ∧
    ∀ z w : Matrix (Fin m) (Fin n) ℂ, brkPP GS GT ξ sS sT z w = 0

end Abstract

section DRho

variable {D : D7}

def ThetaDRho (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → LineAtExists D →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (dRho (heisO ψ S T) θ τ z f) ∧
        ∀ x, HasDerivAt (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f x) (dRho (heisO ψ S T) θ τ z f x) 0

def DRhoLin (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → LineAtExists D →
    ∀ (S T : HSp D) (τ : D.what₂.Tau),
      (∀ (z w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
        dRho (heisO ψ S T) θ τ (z + w) f = dRho (heisO ψ S T) θ τ z f + dRho (heisO ψ S T) θ τ w f) ∧
      (∀ (r : ℝ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
        dRho (heisO ψ S T) θ τ ((r : ℂ) • z) f = (r : ℂ) • dRho (heisO ψ S T) θ τ z f) ∧
      ∀ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        dRho (heisO ψ S T) θ τ z (f + c • g) = dRho (heisO ψ S T) θ τ z f + c • dRho (heisO ψ S T) θ τ z g

open Classical in

def DRhoComm (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → LineAtExists D →
    ∀ (S T : HSp D) (τ τ' : D.what₂.Tau) (z w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f →
      dRho (heisO ψ S T) θ τ z (dRho (heisO ψ S T) θ τ' w f) - dRho (heisO ψ S T) θ τ' w (dRho (heisO ψ S T) θ τ z f) =
        if τ = τ' then (-(2 * Real.pi : ℂ) * Complex.I *
          (eM (gramAt D S τ) (gramAt D T τ) (tauE D τ D.host.xi0) z w : ℂ)) • f else 0

end DRho

section CCR

variable {D : D7}

def aMinusAll {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    FVar D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ) :=
  fun k f => (-((fockScale D k.1 : ℂ)⁻¹)) • annih hs θ k.1 (J k.1) (unitMap (B k.1) (B' k.1) k.2.1 k.2.2) f

structure PairSetup (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) : Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  cartS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)
  cartT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)
  onbS : ∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)
  onbT : ∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)

open Classical in

def CCRTheta (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT →
    IsCCR {f | IsThetaFunO ψ S T f} (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
      (aMinusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)

end CCR

def DRhoSkew (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → LineAtExists D →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
      IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        ∫ w in 𝓕, dRho (heisO ψ S T) θ τ z f w * starRingEnd ℂ (g w) ∂μ =
          -∫ w in 𝓕, f w * starRingEnd ℂ (dRho (heisO ψ S T) θ τ z g w) ∂μ

def ThetaIntO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        IntegrableOn (fun w => f w * starRingEnd ℂ (g w)) 𝓕 μ

def FockNormO (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        ∀ P Q : MvPolynomial (FVar D T.rank S.rank) ℂ,
          ∫ w in 𝓕, pureTensorO ψ θ S T sS sT BS BT f P w * starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT f Q w) ∂μ =
            Formalism.REAL.fockF P Q * ∫ w in 𝓕, f w * starRingEnd ℂ (f w) ∂μ

def NormFockVec (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ,
          nrm2 μ 𝓕 (fockVec (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT P f) =
            (Formalism.REAL.fockF P P).re * nrm2 μ 𝓕 f

section Der

variable {D : D7} {m n : ℕ}

def fCoord (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ) (z : Matrix (Fin m) (Fin n) ℂ)
    (k : Fin m × Fin n) : ℂ :=
  if PosF pS pT k.1 k.2 then (BT⁻¹ * z * BS) k.1 k.2 else starRingEnd ℂ ((BT⁻¹ * z * BS) k.1 k.2)

def adX (XS : Matrix (Fin n) (Fin n) ℂ) (XT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  XT * z - z * XS

def mCoef (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (k l : Fin m × Fin n) : ℂ :=
  fCoord BS BT pS pT ((1 / 2 : ℂ) • (adX XS XT (unitMap BS BT l.1 l.2) -
    cplxO sS sT (adX XS XT (cplxO sS sT (unitMap BS BT l.1 l.2))))) k

def nCoef (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (k l : Fin m × Fin n) : ℂ :=
  fCoord BS BT pS pT ((1 / 2 : ℂ) • (adX XS XT (unitMap BS BT l.1 l.2) +
    cplxO sS sT (adX XS XT (cplxO sS sT (unitMap BS BT l.1 l.2))))) k

open Classical in

def quadOp (τ : D.what₂.Tau) (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (P : MvPolynomial (FVar D m n) ℂ) : MvPolynomial (FVar D m n) ℂ :=
  ∑ k : Fin m × Fin n, ∑ l : Fin m × Fin n,
    (MvPolynomial.C (mCoef sS BS XS sT BT XT pS pT k l) * MvPolynomial.X (τ, k.1, k.2) *
        MvPolynomial.pderiv (τ, l.1, l.2) P +
      MvPolynomial.C (nCoef sS BS XS sT BT XT pS pT k l / 2) * MvPolynomial.X (τ, k.1, k.2) *
        MvPolynomial.X (τ, l.1, l.2) * P -
      MvPolynomial.C (starRingEnd ℂ (nCoef sS BS XS sT BT XT pS pT k l) / 2) *
        MvPolynomial.pderiv (τ, k.1, k.2) (MvPolynomial.pderiv (τ, l.1, l.2) P))

def FockDerO (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    PairSetup ψ θ S T sS sT BS BT pS pT → IsWeilDatumO ψ S T χS χT om →
    ∀ (τ : D.what₂.Tau) (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ → ∃ κ : ℂ,
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P + κ • P) x) 0

def halfTrJ (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ) : ℂ :=
  (1 / 2 : ℂ) * ∑ k : Fin m × Fin n, mCoef sS BS XS sT BT XT pS pT k k

def dOmPol (τ : D.what₂.Tau) (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (αS αT : ℚ) (P : MvPolynomial (FVar D m n) ℂ) : MvPolynomial (FVar D m n) ℂ :=
  quadOp τ sS BS XS sT BT XT pS pT P + (halfTrJ sS BS XS sT BT XT pS pT + (αS : ℂ) * XT.trace - (αT : ℂ) * XS.trace) • P

def RealCharO (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    PairSetup ψ θ S T sS sT BS BT pS pT → IsWeilDatumO ψ S T χS χT om →
    ∀ (τ : D.what₂.Tau) (αS αT : ℚ), HasInfExp D χS τ αS → HasInfExp D χT τ αT →
    ∀ (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
                  (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace -
                    (αT : ℂ) * XS.trace) • P) x) 0

end Der

end Formalism.IndefR.Fock.Sk

end

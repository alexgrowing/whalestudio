import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierCut

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCM

structure Parts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq
  T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j))
  f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))
  χ : ℝ → ℝ
  ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ
  m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r
  top : ∀ j : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin S.f ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

attribute [instance] Parts.pN Parts.pI Parts.qN Parts.qI Parts.pF Parts.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Pins (P : Parts X u u') (CA : ℝ) (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ)
    (l : ℕ) : Prop :=
  P.S.CA = CA ∧ P.S.G = G0 ∧ P.S.de = de ∧ P.S.de' = de' ∧ P.S.l = l ∧ Formalism.L2.SG.DataInst.Compat P.S u u'

def Parts.Built (P : Parts X u u') : Prop := Formalism.FourierDecayAlt.D.IsBuilt P.S P.T P.f P.χ P.ν' P.m₀ P.top P.A₀

def Parts.FromX (P : Parts X u u') : Prop := BuiltFromX X P.S u u' P.T P.f P.τ P.Q P.Qi P.eP P.eQ

def Parts.Base (P : Parts X u u') (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  BaseFromX X P.S u u' i0 i0' P.τ P.Q P.Qi P.ν' P.m₀

def Parts.Top (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  TopTie X P.S u u' sc i0 i0' FdN FdN' νq P.τ

def Parts.Joint (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  VJoint X P.S u u' sc i0 i0' νq P.T P.f P.ν' P.m₀ P.τ P.eP P.eQ

def Parts.Inputs (P : Parts X u u') (C₄ C₆ sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  Formalism.FourierDecayAlt.JCT.BuiltInputs C₄ C₆ P.S P.T P.f P.χ P.ν' P.m₀ P.top P.L P.j P.lam P.c P.Cm P.σ P.Lw P.Ll P.Ll'
    (VtPt X u u' sc i0 i0' FdN FdN' νq)

def Parts.Energy (P : Parts X u u') (jn : ℝ) : Prop := (∏ v, Formalism.FourierDecayAlt.JCT.jvModel P.S P.j P.Cm v) = jn

theorem carrierData_of_parts (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (C₄ jn CA : ℝ)
    (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) (C₆ : ℝ)
    (h1 : P.Pins CA G0 de de' l) (h2 : P.Built) (h3 : P.FromX) (h4 : P.Base i0 i0')
    (h5 : P.Top sc i0 i0' FdN FdN' νq) (h6 : P.Joint sc i0 i0' νq) (h7 : P.Inputs C₄ C₆ sc i0 i0' FdN FdN' νq)
    (h8 : P.Energy jn) :
    CarrierData X u u' sc i0 i0' FdN FdN' νq C₄ jn CA G0 de de' l C₆ :=
  ⟨P.Wp, P.Wq, P.pN, P.pI, P.qN, P.qI, P.pF, P.qF, P.S, P.T, P.f, P.χ, P.ν', P.m₀, P.top, P.A₀, P.τ, P.Q, P.Qi,
    P.eP, P.eQ, P.L, P.j, P.lam, P.c, P.Cm, P.σ, P.Lw, P.Ll, P.Ll', h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1,
    h1.2.2.2.2.1, h1.2.2.2.2.2, h2, h3, h4, h5, h6, h7, h8⟩

end Formalism.L2.SG.Pf.Carrier

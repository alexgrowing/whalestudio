import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp

open NumberField Formalism.BasicNotions Classical

noncomputable section

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7}

def SamePr {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ τ' : D.what₂.Tau) : Prop :=
  ∀ x : 𝓞 D.host.E, ‖tauEmb D lam τ (x : D.host.E)‖ < 1 ↔ ‖tauEmb D lam τ' (x : D.host.E)‖ < 1

def ConjPr {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ τ' : D.what₂.Tau) : Prop :=
  ∀ x : 𝓞 D.host.E, ‖tauEmb D lam τ (x : D.host.E)‖ < 1 ↔ ‖tauEmb D lam τ' (D.host.conj (x : D.host.E))‖ < 1

def dualM {N : ℕ} (M : Matrix (Fin N) (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E :=
  ((M.map D.host.conj).transpose)⁻¹

def AdPl (D : D7) (w : D.what₂.places.Pl) : Prop :=
  D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass ∨ D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal ∨
    D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD

abbrev SysFam (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E

def AdaptedEnt (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) (Dx : DivX D) : Prop :=
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ u μ, LevFree Dx u μ w →
    ∃ Pm : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ, B u μ w i c τ =
        (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ ^ i • (Pm i c τ).map (tauEmb D (P.lam w) τ))

def adCoef {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
    (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  if tauPl D j.1 = k.1 then
    ((P' k.1).map (tauEmb D lam k.1)) k.2.1 j.2.2 * ((P k.1).map (tauEmb D lam k.1))⁻¹ j.2.1 k.2.2
  else 0

def AdaptedTh {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ u μ, LevFree Dx u μ w → ∃ Pm : SysFam D u μ,
    (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (E.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (E.lam w) τ))) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (E.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (E.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) ∧
    ∀ i, i < D.R.m → ∀ c c', E.Th u μ w i c c' =
      atLin (adCoef (E.lam w) (Pm i c) (Pm (i + 1) c')) (fun j => MvPowerSeries.X j) (pSer D (E.lam w) ((O u μ).Th i c c'))

def AdaptedTie {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup} {O : GL3Theta.LiftObj D (D.chTw u μ)}
    {w : D.what₂.places.Pl} (T : GL3Columns.KFTie E O w) : Prop :=
  ∃ (a : D.what₂.Tau → Cw D w) (Pm : SysFam D u μ), (∀ τ, ‖a τ‖ = 1) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (E.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (E.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ, T.B i c τ = a τ ^ i • (Pm i c τ).map (tauEmb D (E.lam w) τ)) ∧
    ∀ i c c' τ, T.c0 i c c' τ * lamC (E.lam w) (O.dgen τ) * a τ = 1

def AdaptedPEx (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Dx : DivX D) : Prop :=
  ∀ (w : D.what₂.places.Pl), AdPl D w → ∀ u μ, LevFree Dx u μ w →
    ∃ Pm : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ))

def DgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ u μ τ, ‖lamC (P.lam w) ((O u μ).dgen τ)‖ = 1

def AdaptedEx (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Dx : DivX D) : Prop :=
  ∃ B : PlaceMatrixFamily D, BasOk P O B ∧ AdaptedEnt P O B Dx

def sysC (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) : SysFam D u μ :=
  Classical.epsilon fun Pm : SysFam D u μ =>
    (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ))

def adBas (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Dx : DivX D) : PlaceMatrixFamily D := fun u μ w i c τ =>
  if AdPl D w ∧ LevFree Dx u μ w then
    (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ ^ i • (sysC P O w u μ i c τ).map (tauEmb D (P.lam w) τ)
  else basC P O u μ w i c τ

def LocBasEx (P : Examples₂.EntPl D) : Prop :=
  letI := D.host.cmStar
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ (N : ℕ) (L : SDLat D.host.E N) (τ : D.what₂.Tau), ∃ M, LocBasisW D (tauEmb D (P.lam w) τ) L.1 M

def OrthoBasEx (P : Examples₂.EntPl D) : Prop :=
  letI := D.host.cmStar
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ (N : ℕ) (L : SDLat D.host.E N) (τ : D.what₂.Tau), ConjPr (P.lam w) τ τ →
    ∃ M, OrthoBasisW D (tauEmb D (P.lam w) τ) L.1 M

def KerEntTied.Adapted {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  AdaptedTh t.ent t.O

end Formalism.L2.Ker

end

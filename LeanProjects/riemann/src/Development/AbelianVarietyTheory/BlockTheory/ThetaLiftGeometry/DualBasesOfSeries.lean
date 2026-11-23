import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualBasesOfSeries

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta
open Classical

def IntJets {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α : σ →₀ ℕ, ‖(α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F‖ ≤ 1

abbrev Var (D : D7) (N N' : ℕ) : Type := (Bool × HH D) × Fin N × Fin N'

def beForm (D : D7) {p : ℕ} [Fact p.Prime] (N N' : ℕ) (u' : HH D → ℂ_[p]) : MvPowerSeries (Var D N N') ℂ_[p] :=
  ∑ t : HH D, MvPowerSeries.C (u' t) * ∑ a : Fin N, ∑ b : Fin N',
    (MvPowerSeries.X ((false, t), a, b) : MvPowerSeries (Var D N N') ℂ_[p]) * MvPowerSeries.X ((true, t), a, b)

def HasShape (D : D7) {p : ℕ} [Fact p.Prime] {N N' : ℕ} (S : ℂ_[p]) (u' : HH D → ℂ_[p])
    (Θ : MvPowerSeries (Var D N N') ℂ_[p]) : Prop :=
  ∃ sg : MvPowerSeries (Var D N N') ℂ_[p], IntJets sg ∧
    Θ = expMv (-(MvPowerSeries.C S * beForm D N N' u')) * sg

abbrev Amb (D : D7) (p : ℕ) [Fact p.Prime] : Type := D.what₂.Tau → ℂ_[p] × ℂ_[p]

def embA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.E) : Amb D p :=
  fun τ => (tauEmb D lam τ a, tauEmb D lam τ (D.host.conj a))

def conjA {D : D7} {p : ℕ} [Fact p.Prime] (x : Amb D p) : Amb D p := fun τ => (x τ).swap

def intA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Set (Amb D p) :=
  closure (Set.range fun a : 𝓞 D.host.E => embA D lam (a : D.host.E))

def latA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → Amb D p) :=
  closure ((fun (y : Fin N → D.host.E) (i : Fin N) => embA D lam (y i)) '' (L : Set (Fin N → D.host.E)))

def DualBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Matrix (Fin N) (Fin N) (Amb D p)) : Prop :=
  (∀ a, (fun i => P i a) ∈ latA D lam L) ∧
  (∀ x ∈ latA D lam L, ∃ c : Fin N → Amb D p, (∀ a, c a ∈ intA D lam) ∧ x = fun i => ∑ a, c a * P i a) ∧
  ∀ a a', ∑ i, P i a * conjA (P i a') = if a = a' then 1 else 0

def atTau {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} (P : Matrix (Fin N) (Fin N) (Amb D p)) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) ℂ_[p] :=
  P.map fun x => (x τ).1

def ellP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    Submodule (PadicComplexInt p) ℂ_[p] :=
  (Submodule.span (PadicComplexInt p) {v : D.what₂.Tau → ℂ_[p] |
      ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), v = fun ρ => tauEmb D lam ρ a}).comap
    (LinearMap.single (PadicComplexInt p) (fun _ : D.what₂.Tau => ℂ_[p]) τ)

def IsGen (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : D.what₂.Tau → ℂ_[p]) : Prop :=
  ∀ τ, ellP D lam τ = Submodule.span (PadicComplexInt p) {g τ}

def chgD (D : D7) {p : ℕ} [Fact p.Prime] {N N' : ℕ} (g : D.what₂.Tau → ℂ_[p])
    (P : HH D → Matrix (Fin N) (Fin N) (Amb D p)) (P' : HH D → Matrix (Fin N') (Fin N') (Amb D p))
    (k : D.what₂.Tau × Fin N' × Fin N) (x : Var D N N') : ℂ_[p] :=
  if tauPl D x.1 = k.1 then
    g k.1 * atTau (P' x.1.2) k.1 k.2.1 x.2.2 * (atTau (P x.1.2) k.1)⁻¹ x.2.1 k.2.2
  else 0

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ

def KerTie (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (idl : D.Dt ⧸ D.UO → IdE D)
    (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ, ∀ i < D.R.m, liftTie D (tor0 D cc δ) (B.eNat (chiRec D idl)) (O u μ) i

def LevTie (D : D7) (Dx : DivX D) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ, ∀ q ∈ (O u μ).S,
    q = (D.mem u).A.T ∨ q ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∨ q ∈ Dx.Qp μ

def GenTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)
    (gen : ∀ w : D.what₂.places.Pl, D.what₂.Tau → ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ w, D.what₂.places.resChar w = D.host.d → IsGen D (E.lam w) (gen w)

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))
    (gen : ∀ w : D.what₂.places.Pl, D.what₂.Tau → ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ u μ w, D.what₂.places.resChar w = D.host.d → LevFree Dx u μ w → ∀ i < D.R.m,
    ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (P : HH D → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Amb D (D.what₂.places.resChar w)))
      (P' : HH D → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) (Amb D (D.what₂.places.resChar w))),
      (∀ t, DualBases D (E.lam w) ((O u μ).lat i c).1 (P t)) ∧
      (∀ t, DualBases D (E.lam w) ((O u μ).lat (i + 1) c').1 (P' t)) ∧
      E.Th u μ w i c c' = linAt (chgD D (gen w) P P') (pSer D (E.lam w) ((O u μ).Th i c c'))

def ShapeD {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = D.host.d →
    ∃ (S : ℂ_[D.what₂.places.resChar w]) (u' : HH D → ℂ_[D.what₂.places.resChar w]),
      ‖S‖ ^ 2 ≤ (D.host.d : ℝ) ∧ (∀ t, ‖u' t‖ ≤ 1) ∧
      ∀ u μ, LevFree Dx u μ w → ∀ i < D.R.m,
        ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape D S u' (E.Th u μ w i c c')

def ShapeD_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (idl : D.Dt ⧸ D.UO → IdE D)
    (O : ∀ u μ, LiftObj D (D.chTw u μ))
    (gen : ∀ w : D.what₂.places.Pl, D.what₂.Tau → ℂ_[D.what₂.places.resChar w]) : Prop :=
  CurveTie D cc δ → RelDetPinned D idl → KerTie D B idl O → LevTie D Dx O → GenTie E gen → SeriesTie E O gen →
    ShapeD E

end GlobalTheory.IndefiniteRowSideFullHecke.DualBasesOfSeries

import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.TeichmullerFactorisation

def laSer (l : ℕ) [Fact l.Prime] {σ : Type} (back : ℕ → σ) : MvPowerSeries σ ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (back e) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laZ (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  laSer l fun e => s - 2 * (e : ZMod d)

def laZ2 (l d : ℕ) [Fact l.Prime] (s : ZMod d) (b : Bool) : MvPowerSeries (ZMod d × Bool) ℂ_[l] :=
  laSer l fun e => (s - 2 * (e : ZMod d), b)

section Beta

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

def CoefProp (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop := GL3Theta.CoefWf be

def TeichInv (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be

def degEven (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if Even s.val then n s else 0

def degOdd (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if Even s.val then 0 else n s

def NoLowTerms (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ n : ZMod d →₀ ℕ, (degEven n = 0 ∨ degOdd n = 0 ∨ (degEven n = 1 ∧ degOdd n = 1)) → MvPowerSeries.coeff n be = 0

def BiaddAt (r : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  GL3Theta.SimeqW
    (MvPowerSeries.subst (fun s : ZMod d =>
      if s.val % 2 = r then laZ2 l d s false + laZ2 l d s true else laZ2 l d s false) be)
    (MvPowerSeries.subst (fun s : ZMod d => laZ2 l d s false) be +
      MvPowerSeries.subst (fun s : ZMod d => if s.val % 2 = r then laZ2 l d s true else laZ2 l d s false) be)

def BetaProps (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  CoefProp be ∧ TeichInv be ∧ NoLowTerms be ∧ BiaddAt 0 be ∧ BiaddAt 1 be

example : NoLowTerms (0 : MvPowerSeries (ZMod d) ℂ_[l]) ∧ TeichInv (0 : MvPowerSeries (ZMod d) ℂ_[l]) :=
  ⟨fun _ _ => by simp, fun _ _ => map_zero _⟩

example : ¬ NoLowTerms (MvPowerSeries.monomial (Finsupp.single (0 : ZMod 2) 1 + Finsupp.single 1 1) (1 : ℂ_[l])) := by
  intro h
  have := h (Finsupp.single (0 : ZMod 2) 1 + Finsupp.single 1 1) (Or.inr (Or.inr ⟨?_, ?_⟩))
  · simp at this
  all_goals
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    have hv : (1 : ZMod 2).val = 1 := rfl
    simp [degEven, degOdd, hu, Finset.sum_pair h01, hv, h01, h01.symm]

end Beta

section Local

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[l])

def embL (x : D.host.E) : D.what₂.Tau → ℂ_[l] × ℂ_[l] :=
  fun τ => (TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ x), TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (D.host.conj x)))

def OEl : Set (D.what₂.Tau → ℂ_[l] × ℂ_[l]) := closure (Set.range fun a : 𝓞 D.host.E => embL D lam (a : D.host.E))

def latL {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l]) :=
  closure ((fun x : Fin N → D.host.E => fun k => embL D lam (x k)) '' (L : Set (Fin N → D.host.E)))

def OrthoL {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (m : Fin N → Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l]) : Prop :=
  (∀ a, m a ∈ latL D lam L) ∧
  (∀ a a' τ, GL3Theta.hP (fun k => m a k τ) (fun k => m a' k τ) = if a = a' then 1 else 0) ∧
  ∀ y ∈ latL D lam L, ∃ c : Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l], (∀ a, c a ∈ OEl D lam) ∧
    y = fun k τ => ∑ a, c a τ * m a k τ

def letter (l : ℕ) (z : Bool × G.HH D) (s : ZMod (G.nP D l)) : Bool × G.HH D := posPl D l z s.val

def BasisO' (z : Bool × G.HH D) (r : ℕ) {k : ℕ} (om : Fin k → D.what₂.Tau → ℂ_[l] × ℂ_[l]) : Prop :=
  (∀ j, om j ∈ OEl D lam) ∧
  ∀ y ∈ OEl D lam, ∃! c : Fin k → ℂ_[l], (∀ j, c j ∈ Prod.fst '' GL3Theta.OKp D lam) ∧
    ∀ s : ZMod (G.nP D l), s.val % 2 = r →
      (y (tauPl D (letter D l z s))).1 = ∑ j, c j * (om j (tauPl D (letter D l z s))).1

def TypeCoords (z : Bool × G.HH D) (r : ℕ) : Prop :=
  ∀ (k : ℕ) (om : Fin k → D.what₂.Tau → ℂ_[l] × ℂ_[l]), BasisO' D lam z r om →
    ∃ t : ZMod (G.nP D l) → MvPowerSeries (Fin k) ℂ_[l],
      (∀ s, MvPowerSeries.constantCoeff (t s) = 0 ∧ GL3Theta.IntegralW (t s)) ∧
      (∃ J' : Matrix (Fin k) {s : ZMod (G.nP D l) // s.val % 2 = r} ℂ_[l], (∀ j s, J' j s ∈ GL3Theta.Wp l) ∧
        (Matrix.of fun (s : {s : ZMod (G.nP D l) // s.val % 2 = r}) (j : Fin k) =>
          MvPowerSeries.coeff (Finsupp.single j 1) (t s.1)) * J' = 1 ∧
        J' * (Matrix.of fun (s : {s : ZMod (G.nP D l) // s.val % 2 = r}) (j : Fin k) =>
          MvPowerSeries.coeff (Finsupp.single j 1) (t s.1)) = 1) ∧
      ∀ s : ZMod (G.nP D l), s.val % 2 = r →
        MvPowerSeries.subst t (laZ l (G.nP D l) s) =
          ∑ j, MvPowerSeries.C (om j (tauPl D (letter D l z s))).1 *
            PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin k) ℂ_[l]) (GL3Theta.logF l)

end Local

abbrev Var (D : D7) (N N' : ℕ) : Type := (Bool × G.HH D) × Fin N × Fin N'

def zOf (D : D7) (l : ℕ) [Fact l.Prime] {N N' : ℕ} (x : Var D N N') : MvPowerSeries (Var D N N') ℂ_[l] :=
  laSer l fun e => (letter D l x.1 (-(2 * (e : ZMod (G.nP D l)))), x.2)

def IsBasePts (D : D7) (l : ℕ) (T : Finset (Bool × G.HH D)) : Prop :=
  ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, posPl D l r e = z

def Factorises (D : D7) (l : ℕ) [Fact l.Prime] (T : Finset (Bool × G.HH D))
    (be : Bool × G.HH D → MvPowerSeries (ZMod (G.nP D l)) ℂ_[l]) {N N' : ℕ}
    (Θ : MvPowerSeries (Var D N N') ℂ_[l]) : Prop :=
  ∃ ε : Bool × G.HH D → ℂ_[l], (∀ z, ‖ε z‖ = 1) ∧
    ∃ U : MvPowerSeries (Var D N N') ℂ_[l], TaylorLogMetric.IntegralMv U ∧
      MvPowerSeries.subst (fun x : Var D N N' => MvPowerSeries.C (ε x.1) * zOf D l x) Θ =
        U * ∏ r ∈ T, TaylorLogMetric.expMv (-∑ a : Fin N, ∑ b : Fin N',
          MvPowerSeries.subst (fun s : ZMod (G.nP D l) => zOf D l ((letter D l r s, a, b) : Var D N N')) (be r))

def InertNotConj (D : D7) (l : ℕ) : Prop :=
  5 ≤ l ∧ (G.IsResidueClassZero D l ∨ G.IsSg D l) ∧ (G.IsResidueClassZero D l → G.HEv D l)

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ

def LevelTie {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ p ∈ O.S, (G.IsResidueClassZero D p ∨ G.IsSg D p) → (p = (D.mem u).A.T ∨ p = D.host.g 0 ∨ p = D.host.g 1 ∨ p ∈ Dx.Qp μ)

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (m : Fin (D.R.N i) → Fin (D.R.N i) → D.what₂.Tau →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (m' : Fin (D.R.N (i + 1)) → Fin (D.R.N (i + 1)) → D.what₂.Tau →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      OrthoL D (E.lam w) (O.lat i c).1 m ∧ OrthoL D (E.lam w) (O.lat (i + 1) c').1 m' ∧ (∀ τ, ‖c0 τ‖ = 1) ∧
      E.Th u μ w i c c' =
        linAt (fun (k : D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i)) (x : Var D (D.R.N i) (D.R.N (i + 1))) =>
          if tauPl D x.1 = k.1 then c0 k.1 * ((m' x.2.2 k.2.1 k.1).1 * (m x.2.1 k.2.2 k.1).2) else 0)
          (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

def Coords_at {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) : Prop :=
  ∀ w : D.what₂.places.Pl, InertNotConj D (D.what₂.places.resChar w) →
    Even (G.nP D (D.what₂.places.resChar w)) ∧
    ∀ z : Bool × G.HH D, TypeCoords D (E.lam w) z 0 ∧ TypeCoords D (E.lam w) z 1

def Shape_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  CurveTie D cc δ χ →
  ∀ w : D.what₂.places.Pl, InertNotConj D (D.what₂.places.resChar w) →
    Nat.Coprime (Ideal.absNorm cc) (D.what₂.places.resChar w) →
    ∃ be : Bool × G.HH D → MvPowerSeries (ZMod (G.nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w],
      (∀ z, BetaProps (be z)) ∧
      ∀ T : Finset (Bool × G.HH D), IsBasePts D (D.what₂.places.resChar w) T →
      ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevFree Dx u μ w → LevelTie Dx u μ O →
      ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i → SeriesTie E u μ O w i →
      ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
        Factorises D (D.what₂.places.resChar w) T be (E.Th u μ w i c c')

def InertStructure_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  Coords_at E ∧ Shape_at D Dx Tw E cc δ B χ

end GlobalTheory.IndefiniteRowSideFullHecke.TeichmullerFactorisation

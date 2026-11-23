import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShapeDegreeParity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

section Local

variable (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]

def laSer (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun α => ∑ e ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

variable {d}

def laAt {σ : Type} (t : ZMod d → MvPowerSeries σ ℂ_[l]) (s : ZMod d) : MvPowerSeries σ ℂ_[l] :=
  MvPowerSeries.subst t (laSer l d s)

def degPar (ε : ℕ) (α : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if s.val % 2 = ε then α s else 0

variable {l}

def CoefB (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop := CoefWf be

def InvB (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if s.val % 2 = 0 then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be

def DegB (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ α : ZMod d →₀ ℕ, (degPar 0 α = 0 ∨ degPar 1 α = 0 ∨ (degPar 0 α = 1 ∧ degPar 1 α = 1)) →
    MvPowerSeries.coeff α be = 0

def AddB (be : MvPowerSeries (ZMod d) ℂ_[l]) (ε : ℕ) : Prop :=
  let z : ZMod d → MvPowerSeries (ZMod d ⊕ ZMod d) ℂ_[l] := laAt l fun s => MvPowerSeries.X (Sum.inl s)
  let z'' : ZMod d → MvPowerSeries (ZMod d ⊕ ZMod d) ℂ_[l] := laAt l fun s => MvPowerSeries.X (Sum.inr s)
  SimeqW (MvPowerSeries.subst (fun s : ZMod d => if s.val % 2 = ε then z s + z'' s else z s) be)
    (MvPowerSeries.subst z be + MvPowerSeries.subst (fun s : ZMod d => if s.val % 2 = ε then z'' s else z s) be)

def IsBeta (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  CoefB be ∧ InvB be ∧ DegB be ∧ AddB be 0 ∧ AddB be 1

end Local

abbrev Lt (D : D7) : Type := Bool × HH D

abbrev Var (D : D7) (N N' : ℕ) : Type := Lt D × Fin N × Fin N'

def CaseA (D : D7) (l : ℕ) : Prop := 5 ≤ l ∧ InertK D l ∧ (IsResidueClassZero D l → Formalism.MainNotions.G.HEv D l)

def IsOrbReps (D : D7) (l : ℕ) (T : Finset (Lt D)) : Prop := ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, posPl D l r e = z

section Coord

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoZ (z : Lt D) : D.host.E → ℂ_[l] := tauEmb D lam (tauPl D z)

def Oprime : Set ℂ_[l] := closure (Set.range fun a : 𝓞 D.host.K => tauK D lam (a : D.host.K))

def Ow (r : Lt D) (ε : ℕ) : Set (ZMod (nP D l) → ℂ_[l]) :=
  closure (Set.range fun a : 𝓞 D.host.E => fun s : ZMod (nP D l) =>
    if s.val % 2 = ε then rhoZ D lam (posPl D l r s.val) (a : D.host.E) else 0)

def IsOwBasis (r : Lt D) (M : Matrix (ZMod (nP D l)) (ZMod (nP D l)) ℂ_[l]) : Prop :=
  (∀ j, (fun s => M s j) ∈ Ow D lam r (j.val % 2)) ∧
  ∀ ε, ε < 2 → ∀ y ∈ Ow D lam r ε, ∃ c : ZMod (nP D l) → ℂ_[l],
    (∀ j, c j ∈ Oprime D lam) ∧ (∀ j, j.val % 2 ≠ ε → c j = 0) ∧ y = M.mulVec c

def CoordT (r : Lt D) : Prop :=
  (∃ M, IsOwBasis D lam r M) ∧
  ∀ M, IsOwBasis D lam r M → ‖M.det‖ = 1 ∧
    ∃ t : ZMod (nP D l) → MvPowerSeries (ZMod (nP D l)) ℂ_[l],
      (∀ s, IntegralW (t s) ∧ MvPowerSeries.constantCoeff (t s) = 0 ∧
        ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (t s) = M s j) ∧
      ∀ s, laAt l t s = ∑ j, MvPowerSeries.C (M s j) *
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (ZMod (nP D l)) ℂ_[l]) (logF l)

def IsBases {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (P : Lt D → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  ∀ z, LocBasisW D (rhoZ D lam z) L (P z) ∧ ((P (posPl D l z 1)).map D.host.conj).transpose * P z = 1

def readIn {N N' : ℕ} (c : Lt D → ℂ_[l]) (P : Lt D → Matrix (Fin N) (Fin N) D.host.E)
    (P' : Lt D → Matrix (Fin N') (Fin N') D.host.E) (F : MvPowerSeries (Idx D N N') ℂ_[l]) :
    MvPowerSeries (Var D N N') ℂ_[l] :=
  linAt (fun (k : Idx D N N') (x : Var D N N') =>
    if tauPl D x.1 = k.1 then
      c x.1 * ((P' x.1).map (rhoZ D lam x.1)) k.2.1 x.2.2 * (((P x.1).map (rhoZ D lam x.1))⁻¹) x.2.1 k.2.2
    else 0) F

variable (l)

def zSer {N N' : ℕ} (x : Var D N N') : MvPowerSeries (Var D N N') ℂ_[l] :=
  laAt l (fun s : ZMod (nP D l) => MvPowerSeries.X ((posPl D l x.1 s.val, x.2) : Var D N N')) 0

variable {l}

def beSum (N N' : ℕ) (r : Lt D) (be : MvPowerSeries (ZMod (nP D l)) ℂ_[l]) : MvPowerSeries (Var D N N') ℂ_[l] :=
  ∑ a : Fin N, ∑ b : Fin N',
    MvPowerSeries.subst (fun s : ZMod (nP D l) => zSer D l ((posPl D l r s.val, a, b) : Var D N N')) be

def Shape {N N' : ℕ} (T : Finset (Lt D)) (be : Lt D → MvPowerSeries (ZMod (nP D l)) ℂ_[l]) (κ : Lt D → ℂ_[l])
    (Θ : MvPowerSeries (Var D N N') ℂ_[l]) : Prop :=
  ∃ U : MvPowerSeries (Var D N N') ℂ_[l], IntegralMv U ∧
    MvPowerSeries.subst (fun x : Var D N N' => MvPowerSeries.C (κ x.1) * zSer D l x) Θ =
      U * ∏ r ∈ T, expMv (-beSum D N N' r (be r))

end Coord

def CombShape (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), CaseA D l → Nat.Coprime (Ideal.absNorm cc) l →
    (∀ r, CoordT D lam r) ∧
    ∃ (ep : ℂ_[l]) (be : Lt D → MvPowerSeries (ZMod (nP D l)) ℂ_[l]),
      ep ∈ Wp l ∧ ‖ep‖ = 1 ∧ (∀ r, IsBeta (be r)) ∧
      ∀ T, IsOrbReps D l T →
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : Lt D → Matrix (Fin N) (Fin N) D.host.E) (P' : Lt D → Matrix (Fin N') (Fin N') D.host.E)
        (F : MvPowerSeries (Idx D N N') ℂ_[l]),
        admitted D N N' L L' → IsBases D lam L P → IsBases D lam L' P' → IsComb D (tor0 D cc δ) e lam L L' F →
        Shape D T be (fun _ => ep) (readIn D lam (fun _ => 1) P P' F)

def KerTie (D : D7) (T : Tor D) (e : FamE D) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
    (O : LiftObj D C) (i : ℕ) : Prop :=
  ∀ c c', IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')

def ThTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (O : LiftObj D (D.chTw u μ)) (i : ℕ)
    (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : Prop :=
  ∃ (P : Lt D → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
    (P' : Lt D → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E)
    (c0 : Lt D → ℂ_[D.what₂.places.resChar w]),
    IsBases D (E.lam w) (O.lat i c).1 P ∧ IsBases D (E.lam w) (O.lat (i + 1) c').1 P' ∧
    (∀ z, ‖c0 z‖ = ‖lamC (E.lam w) (O.dgen (tauPl D z))‖) ∧
    E.Th u μ w i c c' = readIn D (E.lam w) c0 P P' (pSer D (E.lam w) (O.Th i c c'))

def KerShape (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ w : D.what₂.places.Pl, CaseA D (D.what₂.places.resChar w) →
    Nat.Coprime (Ideal.absNorm cc) (D.what₂.places.resChar w) →
    (∀ r, CoordT D (E.lam w) r) ∧
    ∃ be : Lt D → MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w],
      (∀ r, IsBeta (be r)) ∧
      ∀ T, IsOrbReps D (D.what₂.places.resChar w) T →
      ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), LevFree Dx u μ w →
      ∀ O : LiftObj D (D.chTw u μ), D.what₂.places.resChar w ∉ O.S →
      ∀ i, i < D.R.m → KerTie D (tor0 D cc δ) e O i →
      ∀ c c', ThTie E u μ w O i c c' →
        ∃ κ : Lt D → ℂ_[D.what₂.places.resChar w], (∀ z, ‖κ z‖ = 1) ∧ Shape D T be κ (E.Th u μ w i c c')

def StrA_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → vec22 D (tor0 D cc δ) e → int22 D (tor0 D cc δ) e →
    KerShape D Dx Tw E cc δ e

def StrA_nat (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) : Prop :=
  IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → KerShape D Dx Tw E cc δ (B.eNat χ)

def StrA_comb (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → int22 D (tor0 D cc δ) e → CombShape D cc δ e

end GlobalTheory.IndefiniteRowSideFullHecke.ShapeDegreeParity

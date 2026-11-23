import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.SharpRestriction.Divisibility.JumpSets
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LIncl {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) : Prop :=
  ∀ z ∈ B.cutZ ℓ Z, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z)

def Covers {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)
    (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} {I : Type}
    (X : I → HidaSetting ι N lam) : Prop :=
  ∀ J : ℕ, (∀ i, (X i).Incl (Formalism.EigenvalueLevelCeiling.plc w) J) → LIncl B ℓ Z w J

def reFr {ι : Type} (W : Wts ι) (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) : Wts ι := { W with fr := fr, cj := cj }

variable {D : D7}

structure Dict (L : SizeData₂ D) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) : Prop where
  k : P.k = D.R.k
  m : P.m = D.R.m
  t : P.t = D.R.t
  f : P.f = D.R.f
  card : Nat.card D.what₂.Tau = P.f
  Nr : P.Nr = (Vc D j).rank
  x : P.x = L.sc.x
  log : P.L = L.sc.x ^ L.sc.eps
  b : P.b = L.sc.b
  lam : ∀ τ, ∃ c : ℤ, ∀ a : Fin (Vc D j).rank,
    (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).w a + c
  forced : ∀ τ, Formalism.IndefR.Bridge.IsLamPrime (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ
  box : ∀ τ a, a < P.Nr → 0 ≤ W.U P τ a ∧ W.U P τ a ≤ (h0 P : ℤ)
  thick : W.T2.card ≤ D.host.T2.card
  special : W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet D
  big : ∀ i, P.h < (D.host.g i : ℝ)

def NumOk {ι : Type} (P : Par) (W : Wts ι) : Prop :=
  P.Hyp ∧ P.Large ∧ W.Ok P ∧ ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows P X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big P.L P.x X' A

theorem LIncl.succ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : LIncl B ℓ Z w (J + 1) := fun z hz => by
  rw [pow_succ', mul_smul]
  exact Submodule.smul_mem _ _ (h z hz)

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev blk (j : Fin D.R.m) (t : p.P.T) := p.P.A3.A.fam.L j t

abbrev lvlL := p.P.A3.A.fam.lvlA p.P.P0 p.P.ψ0

abbrev subZ (j : Fin D.R.m) (t : p.P.T) : Submodule D.what₂.LL (blk p j t).S.Forms :=
  (p.P.A3.fam3.toSub2 (p.R.toCx3 p.F).zs).Zl j t

open Classical in

def ModelAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ (fr : ℕ → D.what₂.Tau → D.what₂.Tau) (cj : ℕ → D.what₂.Tau → Bool) (I : Type) (X : I → HidaSetting D.what₂.Tau P.Nr W.lam),
    Covers (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w X ∧
      ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)

end Point

def NumSt : Prop := AtPts fun Fm x _ i _ => ∀ j, ∃ (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W ∧ NumOk P W

open Classical in

def SumExpSt : Prop := AtPts fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w))

def ModelSt : Prop := AtPts fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j P W w

end GlobalTheory.ExpTie

end

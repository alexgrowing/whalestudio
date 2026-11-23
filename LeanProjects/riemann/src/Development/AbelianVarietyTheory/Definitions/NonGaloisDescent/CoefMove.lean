import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TowerCov

open NumberField IsDedekindDomain
open scoped TensorProduct
open Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure LevTie {E : ExpSet D} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (Cv : LevN E → Cover T j σ) : Prop where
  unif : ∀ N, (Cv N).IsUnif
  pos : ∀ N : LevN E, 0 < (Cv N).d.l₂.M
  dvd : ∀ N : LevN E, N.1 ∣ (Cv N).d.l₂.M
  pl : ∀ N, ∀ PP ∈ E.Pg ∪ E.Pd, (((Cv N).d.l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  modu : ∀ N : LevN E, ∃ q : ℕ, modN E N.1 ∣ (Cv N).d.l₂.M * q ∧ Nat.Coprime q N.1 ∧
    ∀ PP ∈ E.Pg ∪ E.Pd, ((q : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  curve : ∀ N, GlobalTheory.FinalJoin.WeberIn T.Q.H (Cv N).d.c₂.F (Cv N).d.l₂.M ∨
    GlobalTheory.CompRat.CurveOver T.Q.H (Cv N).d.c₂.F (Cv N).d.l₂.M
  lat : (E.ΛW : Set (Fin E.W.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D E.W

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ExpTie (E : ExpSet D) (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0) : Prop where
  hV : E.V = Vc D i
  hW : E.W = Wc D i
  ψ : E.ψ = R.ψ
  θ : E.θ = R.θ
  sV : HEq E.sV (fun _ : D.what₂.Tau => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ))
  sW : HEq E.sW (cart (R.MW i (sg0 D A)))
  BV : HEq E.BV (R.BV i)
  BW : HEq E.BW (onb (R.MW i (sg0 D A)))
  ΛV : HEq E.ΛV (R.ΛV i)
  ΛW : HEq E.ΛW (R.ΛW i)
  βV : HEq E.βV (R.βV i)
  βW : HEq E.βW (R.βW i)
  χV : E.χV = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
  χW : E.χW = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2
  om : HEq E.om (R.ωP i t)
  f₀ : HEq E.f₀ (R.vacP i)
  gp : E.gp = D.host.g
  Pg : E.Pg = R.Pg
  Pd : E.Pd = R.Q t
  pde : E.pde = ![D.host.pde, D.host.pde']

def IsHarm (E : ExpSet D) (R : RealDat D A Ks) (i : Fin D.R.m) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (X : Set (R.cV i).W)
    (p : MvPolynomial (FVar D E.W.rank E.V.rank) ℂ) : Prop :=
  ∃ w ∈ X, HEq p (R.ioP i (PiTensorProduct.tprod ℂ u) w)

def CoefMove (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) : Prop :=
  ∀ γ ∈ GQ E.V, ∀ s ∈ GfC E.V, ∀ s' ∈ GfC E.V, finHom E.V s' = finHom E.V (γ * s) → ∀ P' ∈ C.LL s', ∃ P ∈ C.LL s,
    ∀ (e : AE D) (Φ φ : WO E.V E.W → ℂ),
      IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) e (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
        serAt E C s' φ P' = serAt E C s φ P

end GlobalTheory.TowerCov

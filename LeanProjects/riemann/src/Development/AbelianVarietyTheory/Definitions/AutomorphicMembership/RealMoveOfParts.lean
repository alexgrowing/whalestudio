import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi

noncomputable section

section Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.L2 (NExpTied)
open Formalism.L2.Host (embLL0 CharFrame)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.SerMove

variable {D D' : D7}

structure BigHost (D : D7) : Prop where
  host : HostHyp D
  std : ∀ j, FWT.VStd D j
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

structure Frames (X : RealSide D) (X' : RealSide D') : Prop where
  Pg : HEq X.R.Pg X'.R.Pg
  ψ : HEq X.R.ψ X'.R.ψ
  θ : HEq X.R.θ X'.R.θ
  ΛV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.ΛV j) (X'.R.ΛV j')
  ΛW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.ΛW j) (X'.R.ΛW j')
  βV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.βV j) (X'.R.βV j')
  βW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.βW j) (X'.R.βW j')
  BV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.BV j) (X'.R.BV j')
  vacP : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.vacP j) (X'.R.vacP j')
  MW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → SameModel (model X j) (model X' j')
  v₀ : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    SameVec (X.geo.v₀ j (sg0 D X.A3.A)) (X'.geo.v₀ j' (sg0 D' X'.A3.A))

structure Chars (X : RealSide D) (X' : RealSide D') : Prop where
  eta : HEq X.R.eta X'.R.eta
  mu0 : ∀ (j : Fin D.R.m), HEq (X.R.mu0 ((j : ℕ) + 1)) (X'.R.mu0 ((j : ℕ) + 1))
  Cmu0 : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.C.mu0 j) (X'.R.C.mu0 j')
  delAt : ∀ l, HEq (X.R.C.delAt l) (X'.R.C.delAt l)

structure Grps (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) (γ : X.Γ ≃* X'.Γ) : Prop where
  eG : ∀ g, HEq (X.R.eG g) (X'.R.eG (γ g))
  cG : HEq X.cG X'.cG
  P0 : ∀ g, g ∈ X.F.P0 ↔ γ g ∈ X'.F.P0
  ψ0 : ∀ (g : X.F.P0) (g' : X'.F.P0), γ g = g' → (X'.F.ψ0 g' : D'.what₂.LL) = ι (X.F.ψ0 g : D.what₂.LL)

def PlCl (X : RealSide D) (X' : RealSide D') : Prop :=
  ∀ i' t' P', P' ∈ X'.R.Q t' → P' ∈ D'.ntw.pD i' → ∃ t, ∃ P ∈ X.R.Q t, HEq P P'

def IoCl (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) : Prop :=
  ∃ c0L c0L', IsCoef X c0L ∧ IsCoef X' c0L' ∧ ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    ∀ (u : ∀ τ, lowT (model X j) τ) (u' : ∀ τ, lowT (model X' j') τ), SameVec (M := model X j) (M' := model X' j') (fun τ => u τ) (fun τ => u' τ) →
    ∀ (F : VV D.what₂.LL (FWT.lamV D j)) (F' : VV D'.what₂.LL (FWT.lamV D' j')),
      HEq (MvPolynomial.map ι (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
        (F' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' j').rank) →
      HEq (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) (X'.R.ioP j' (PiTensorProduct.tprod ℂ u') (c0L' j' F'))

def FormsCl (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) (eK : X.core.Q.c.F ≃+* X'.core.Q.c.F)
    (γ : X.Γ ≃* X'.Γ) : Prop :=
  ∃ forms : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → KsIso ι eK γ (X.R.FW j) (X'.R.FW j'),
  ∀ (j : Fin D.R.m) (j' : Fin D'.R.m) (h : (j : ℕ) = j') (x : (X.R.FW j).WK),
    SameMap (evidence X j x) (evidence X' j' ((forms j j' h).φ x))

theorem realMove_of_parts {X : RealSide D} {X' : RealSide D'} {ι : D.what₂.LL →+* D'.what₂.LL} {eK : X.core.Q.c.F ≃+* X'.core.Q.c.F}
    {γ : X.Γ ≃* X'.Γ} (a : Frames X X') (b : Chars X X') (c : Grps X X' ι γ) (q : PlCl X X') (o : IoCl X X' ι)
    (s : FormsCl X X' ι eK γ) : Nonempty (RealMove X X' ι) :=
  let ⟨forms, hr⟩ := s
  ⟨{ eK := eK, γ := γ, forms := forms, read := hr, Q := q, io := o, Pg := a.Pg, ψ := a.ψ, θ := a.θ, ΛV := a.ΛV, ΛW := a.ΛW, βV := a.βV, βW := a.βW, BV := a.BV, vacP := a.vacP, MW := a.MW, v₀ := a.v₀,
     eta := b.eta, mu0 := b.mu0, Cmu0 := b.Cmu0, delAt := b.delAt, eG := c.eG, cG := c.cG, P0 := c.P0, ψ0 := c.ψ0 }⟩

end GlobalTheory.HeightCounting.SerMove

end Abstract

section States

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.SerMove

variable {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}

abbrev Geo (x : St P) := GlobalTheory.RealGeo.GeoHalf x.m.z.core x.m.z.R.toRealDat fun _ => 1

abbrev datAt (x : St P) (g : Geo x) : Dat (w.st x.o.Z) w.I P.hX T P.Wt := { x.m.z with geo := g }

theorem finite_tup (P : Pre2 K w) : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
  have hs : ({τ | τ = (Formalism.L2.DIV.mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
      Set _).Finite :=
    (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
  exact hs.to_subtype

def sideAt (x : St P) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) : GlobalTheory.TwInputs.RealSide (Dof x) :=
  GlobalTheory.TwInputs.RealSide.ofPins g x.m.z.pins x.m.intersectionNumber_baseChange hg (finite_tup P) a.host a.std a.size

structure Link (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0)
    (g : Geo x) (g' : Geo x') : Prop where
  ov : K.Over B'.toPre
  kpx : KPx B' f'
  forced : Forced K B' T'
  start' : Start K B' f' T' w'
  enl : Enl B B'
  fr : HEq f' f
  start : Start K B f T w
  px : HEq w'.px w.px
  sel : HEq w'.I.sel w.I.sel
  J : HEq w'.I.J w.I.J
  δ : HEq w'.δ w.δ
  ext : Ext P.z P'.z
  cp : GlobalTheory.TwInputs.Move.CopyTw (Dof x) (Dof x') ι e
  gal : SameGal (Dof x) (Dof x')
  extN : ExtN (datAt x g) (datAt x' g')

end GlobalTheory.HeightCounting.SerMove

end States

end

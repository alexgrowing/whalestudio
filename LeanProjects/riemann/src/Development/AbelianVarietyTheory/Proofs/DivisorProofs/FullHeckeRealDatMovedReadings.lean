import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnframePt

open GlobalTheory.RealGeo GlobalTheory.Unframe Formalism.IndefR.FWT

abbrev fullHeckeRealDatMovedReadings {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) : RealDat3 D A3 Ks :=
  { Rl with toRealDat := moveR Rl.toRealDat w }

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def geoHalf (p : PtAt ex Csz) : GeoHalf p.T p.R.toRealDat (fun _ => 1) :=
  ⟨p.κ, p.v₀, p.fw, p.bar, p.O, p.pins, p.rhoGeo, p.equivAll, p.cTie, fun i hu => by
    have e : phEff p.R = fun _ => (1 : ℂ) := funext p.phEff_one
    rw [← e]
    exact p.phase i hu⟩

end Pt

end GlobalTheory.UnframePt

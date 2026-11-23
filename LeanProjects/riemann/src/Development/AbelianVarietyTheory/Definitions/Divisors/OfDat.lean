import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {Tw : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}

theorem TiesA.of_dat (z : Dat X I hX Tw Wt)
    (ok : (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).fam3.Ok3 1) (hex : z.R.toRealDat.ExAt)
    (host : Formalism.IndefR.Links.HostHyp X.toD7) (par : ∃ L : SizeData₂ X.toD7, Nonempty (ParameterChoice' X.toD7 L))
    (ty : GlobalTheory.Mem.Top.TypesTrue X.toD7.ntypes z.R.C.P z.R.C.W) (ser : SerClause X.toD7)
    (w1 : ∀ w, (z.R.toCx3 z.F).W1 z.F.cr (z.R.num z.F 0 0) w → w ∈ z.R.twPl)
    (nV : 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) : TiesA z.R z.F :=
  ⟨ok, z.pins.char, hex, host, par, X.B.ccK_top, z.pins.keep.guard,
    GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue z.pins.char.base.lev ty, ser,
    GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, z.pins.trSem, z.pins.keep.std, z.pins.phs, w1, nV⟩

theorem TiesG.of_dat (z : Dat X I hX Tw Wt) (hU : z.R.toRealDat.LUnif) (hI : IoExt z.R.toRealDat)
    (hM : ∀ i, OneMapRowR z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O (fun _ => 1) i)
    (hC : GlobalTheory.TwistField.CoverField z.core z.R.toRealDat) : TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O := by
  have e : (fun i => cj (twAt X.toD7.what₂.embLL (famR X I hX (usedOf I Tw Wt) z.Xg z.tr).A.v0) (z.R.phs i)) = fun _ => (1 : ℂ) := by
    funext i
    rw [z.pins.phs i]
    exact map_one _
  refine ⟨⟨z.geo.fw, z.geo.bar⟩, z.geo.pins, ?_, hU, hI, ?_, hC⟩
  · rw [e]; exact z.geo.phase
  · rw [e]; exact hM

end GlobalTheory.PrimIn

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm
open GlobalTheory.LB (toMod)

namespace GlobalTheory.ThetaRR

theorem exists_lb_of_pushInvertible {S : Scheme.{0}} (G : Over S) (L : LB G.left) (h : PushInvertible G L) :
    ∃ M : LB S, M.IsLB ∧ Nonempty (toMod M ≅ (Scheme.Modules.pushforward G.hom).obj (toMod L)) := by
  choose U hU θ hθ gen _ using h
  let e : ∀ x, Γ((Scheme.Modules.pushforward G.hom).obj (toMod L), U x) := fun x => GlobalTheory.LB.mkSec (θ x) (hθ x)
  have he : ∀ x, GlobalTheory.LB.IsFrame (e x) := fun x W hW => by
    rw [Function.bijective_iff_existsUnique]
    intro s
    refine (existsUnique_congr fun a => ?_).1 (gen x W hW _ (GlobalTheory.LB.coord_mem (L := L) s))
    exact ⟨fun e => GlobalTheory.LB.sec_ext (L := L) fun i => (e i).symm,
      fun e i => (congrArg (fun s => GlobalTheory.LB.coord (L := L) s i) e).symm⟩
  have hc : ⨆ x, U x = ⊤ := top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hU x⟩
  exact ⟨_, GlobalTheory.LB.ofFrames_isLB he hc, ⟨(GlobalTheory.LB.ofFramesIso he hc).symm⟩⟩

theorem exists_lb_pushforward : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p →
    ∀ (P : PPAS S) (L : LB P.A.left), IsTheta P L →
      ∃ M : LB S, M.IsLB ∧ Nonempty (toMod M ≅ (Scheme.Modules.pushforward P.A.hom).obj (toMod L)) := by
  intro k _ S p hS P L hL
  obtain ⟨N, j, _, hj⟩ := hS.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have := hS.finite
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  exact exists_lb_of_pushInvertible P.A L
    (GlobalTheory.PushInv.pushInvertible GlobalTheory.abelianSchemeLaws_all.1.secBaseChange S hL.polAV)

end GlobalTheory.ThetaRR

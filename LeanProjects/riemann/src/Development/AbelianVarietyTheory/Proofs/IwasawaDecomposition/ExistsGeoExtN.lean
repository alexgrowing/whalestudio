import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesOfLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.StateChecks

namespace GlobalTheory.HeightCounting.SerMove.ReGeo

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

set_option maxHeartbeats 4000000 in

theorem geo_copy {Z Z' : w.Lt} (z₀ : Dat (w.st Z) w.I hX T Wt) (z : Dat (w.st Z') w.I hX T Wt) (h1 : z.Xg = z₀.Xg)
    (h2 : z.tr = z₀.tr) (h3 : HEq z.core (coreJ (a := Z) Z' z₀.core)) (h4 : HEq z.R (real3 (a := Z) Z' (iK := z₀.alg) z₀.R))
    (hg : GlobalTheory.RealGeo.InGeo z₀.geo) :
    ∃ g : GlobalTheory.RealGeo.GeoHalf z.core z.R.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo g ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z₀ z' → ExtN { z with geo := g } z') ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z' z₀ → ExtN z' { z with geo := g }) := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4 ⊢
  subst h1 h2
  obtain rfl : core = coreJ (a := Z) Z' z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg (a := Z) Z' z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR (a := Z) Z' z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR (a := Z) Z' z₀)) :))))
  refine ⟨(by with_unfolding_all exact ((geoHalf (a := Z) Z' (iK := z₀.alg) z₀.geo) :)), (by with_unfolding_all exact ((inGeo_tr (a := Z) Z' (iK := z₀.alg) hg) :)), ?_, ?_⟩
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }

end GlobalTheory.HeightCounting.SerMove.ReGeo

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_geo_extN : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}, Ext P.z P'.z → ∀ (x : St P) (x' : St P'), ∃ (g : Geo x) (g' : Geo x'), GlobalTheory.RealGeo.InGeo g ∧ GlobalTheory.RealGeo.InGeo g' ∧ ExtN (datAt x g) (datAt x' g') := by
  intro K B B' f f' T T' w w' P P' e x x'
  obtain ⟨g, hg, hL, -⟩ := ReGeo.geo_copy (Z := P.Z₀) (Z' := x.o.Z) P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.inGeo
  obtain ⟨g', hg', -, hR⟩ :=
    ReGeo.geo_copy (Z := P'.Z₀) (Z' := x'.o.Z) P'.z x'.m.z x'.m.Xg x'.m.tr ((by with_unfolding_all exact (x'.copy.core :))) ((by with_unfolding_all exact (x'.copy.R :))) P'.inGeo
  exact ⟨g, g', hg, hg', hR _ (hL _ e.extN)⟩

end GlobalTheory.HeightCounting.SerMove

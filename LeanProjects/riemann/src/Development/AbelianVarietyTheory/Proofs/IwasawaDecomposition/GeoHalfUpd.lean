import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RealGeo.Upd

section
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section
variable (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (kap lam err)

abbrev upE : RealDat D A C.Q.c.F := { R.upd6 kap lam with err0 := err }

set_option maxHeartbeats 1600000 in

def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat C.toCore R i Tp tup) :
    OMDat C.toCore (upE C R kap lam err) i Tp tup := { O with }

set_option maxHeartbeats 1600000 in

def updFWT {κ v₀} (t : FWTie C R κ v₀) : FWTie C (upE C R kap lam err) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

variable {C R}
variable {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (O : ∀ i, OMDat C.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in

theorem omPins_upE (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (upE C R kap lam err) κ v₀ (fun i => updO C R kap lam err (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end

end

end GlobalTheory.RealGeo.Upd

namespace GlobalTheory.RealGeo

set_option maxHeartbeats 1600000 in

theorem geoHalf_upd : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (ph : Fin D.R.m → ℂ) kap lam err (g : GlobalTheory.RealGeo.GeoHalf C R ph), ∃ g' : GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph, g'.κ = g.κ ∧ HEq g'.v₀ g.v₀ ∧ (GlobalTheory.RealGeo.InGeo g → GlobalTheory.RealGeo.InGeo g') := by
  intro D G _ _ Pl0 T A C _ R ph kap lam err g
  refine ⟨⟨g.κ, g.v₀, Upd.updFWT C R kap lam err g.fw, g.bar, fun i => Upd.updO C R kap lam err (g.O i),
    fun i => Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩, rfl, HEq.rfl, ?_⟩
  intro h
  exact ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

end GlobalTheory.RealGeo

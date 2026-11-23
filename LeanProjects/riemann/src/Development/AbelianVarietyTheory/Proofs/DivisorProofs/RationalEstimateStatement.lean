import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassSumsRationalOfRayClassFieldsStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 1000000 in

theorem oneMapRowR_charOf (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : Fin D.R.m → ℂ)
    (i : Fin D.R.m) (h : OneMapRowR J R κ v₀ O ph i) :
    OneMapRowR J (charOf R F) κ v₀ (fun k => reOM (O k) F) ph i := by
  refine ⟨?_, fun hq => ?_⟩
  · obtain ⟨cc, ph', h0⟩ := h.1
    exact ⟨cc, ph', h0⟩
  · obtain ⟨O', h1, h2, h3⟩ := h.2 hq
    refine ⟨{ O' with }, h1, ⟨⟨h2.lift.field, h2.lift.std, h2.lift.v0, h2.lift.c0, h2.lift.lev⟩,
      fun t => ⟨(h2.tuple t).reps, (h2.tuple t).B, (h2.tuple t).xi, (h2.tuple t).phi, (h2.tuple t).half⟩,
      h2.act, h2.bad, h2.reps, h2.ep, h2.io, h2.w, h2.cov, h2.cxi, h2.model₂⟩, h3⟩

end Gen

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem phEff_eq_one : phEff p.R = fun _ => 1 := by
  funext i
  simp [phEff, p.phsOne i]

theorem extremal_vectors_split_part (h : p.Rows) : IoExt (R2 p) := h.ioExt

theorem splitPartRealisation_satisfies_qGuard : QGuard (R2 p) := p.qGuard

theorem one_map_split_part (h : p.Rows) (i : Fin D.R.m) : OneMapRowR p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have := oneMapRowR_charOf (κ := p.κ) (v₀ := p.v₀) p.O (F2 p) (phEff p.R) i (h.oneMap i)
  rw [phEff_eq_one] at this
  exact this

theorem twistedRational_at (h : p.Rows) (hm : More p) : GlobalTheory.RealIndexBound.TwistedRational (R2 p) (F2 p) fun _ => 1 := by
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p h hm.1
  exact GlobalTheory.T.twistedClassSums_rational_of_rayClassFields D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hL.1 (extremal_vectors_split_part p h) hL.2.2.1
    hL.2.2.2.2.2.2.1 (splitPartRealisation_satisfies_qGuard p) (one_map_split_part p h) hL.2.2.2.1 hL.2.2.2.2.1 hm.2.2.rayQ

end Point

theorem ratSt : RatSt :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p h hm => twistedRational_at p h hm⟩⟩⟩

end GlobalTheory.BigOn

end

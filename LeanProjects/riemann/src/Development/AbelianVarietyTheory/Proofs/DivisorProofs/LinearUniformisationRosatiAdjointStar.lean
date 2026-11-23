import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OLinRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

omit [IsDomain R] in

theorem thickMap_pullback_map {G : Over (Sp R)} (b : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem linEnd_act {D : DegData R I} {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.toPre.OAct O}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) :
    LinEnd U (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (oG.act a) := by
  haveI := oG.hom a
  refine ⟨oG.hom a, fun e => inferInstance, fun e => thickMap_pullback_map _ e, fun e => h.q_lin e a, fun e => ?_⟩
  exact h.i_lin e a

theorem endData_act {D : DegPre R} {O : Type} [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (a : O) :
    EndData D (o.onB.act a) (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨o.onB.hom a, o.onB.hom (star a), o.onB.rosati a, o.c_lin a, o.c_lin (star a), o.tau_bal a⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D O _ _ _ o A G _ _ U oA oG hG hlin a
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have h₁ := linEnd_act hlin a
  have h₂ := linEnd_act hlin (star a)
  rw [star_star] at h₂
  exact linEnd_adjoint_lbIso R hB D A G hG U _ _ _ _ (endData_act o a) _ _ h₁ h₂

end GlobalTheory.Mum.OLinRosati

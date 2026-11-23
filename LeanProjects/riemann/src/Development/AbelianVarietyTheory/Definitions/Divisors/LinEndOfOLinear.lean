import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ConclusionNotEmpty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.EndModel
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem endData_tate (m : ℤ) :
    EndData tatePre (𝟙 _) (𝟙 _) (AddMonoidHom.mulLeft m) (AddMonoidHom.mulLeft m) := by
  refine ⟨inferInstance, inferInstance, GlobalTheory.BoxPowerProbe.rosati_tate, fun _ => (Category.comp_id _).symm,
    fun _ => (Category.comp_id _).symm, ?_⟩
  exact (GlobalTheory.BoxPowerProbe.tauBal_tate_iff _ _).2 fun y y' => by
    show m * y * y' = y * (m * y'); ring

theorem not_endData_tate :
    ¬ EndData tatePre (𝟙 _) (𝟙 _) 0 (AddMonoidHom.id _) := fun h => by
  have := (GlobalTheory.BoxPowerProbe.tauBal_tate_iff _ _).1 h.2.2.2.2.2 1 1
  change (0 : ℤ) * 1 = 1 * 1 at this
  simp at this

theorem endData_of_oAct {R : Type} [CommRing R] [IsDomain R] (O : Type) [Ring O] [StarRing O] (D : DegPre R)
    [Module O D.X] (io : D.OAct O) (a : O) :
    EndData D (io.onB.act a) (io.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨io.onB.hom a, io.onB.hom (star a), io.onB.rosati a, io.c_lin a, io.c_lin (star a), io.tau_bal a⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem torusEndOf_id {S : Scheme.{0}} (X : Type) [AddCommGroup X] :
    TorusEndOf X (AddMonoidHom.id X) (𝟙 (splitTorus S X)) :=
  (GlobalTheory.LinearUnifCheck.torusEndOf_iff _ _).2 fun χ => by simp

theorem linEnd_id (U : UnifPre I D A G) : LinEnd U (𝟙 _) (AddMonoidHom.id _) (𝟙 G) := by
  refine ⟨inferInstance, fun e => by simpa using (inferInstance : IsMonHom (𝟙 _)), fun e => by simp,
    fun e => by simp, fun e => ⟨𝟙 _, torusEndOf_id _, by simp⟩⟩

theorem thickMap_map {G H : Over (Sp R)} (b : G ⟶ H) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e H := by
  apply pullback.hom_ext
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
    rfl
  · simp only [thickMap, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    simp
    erw [pullback.lift_snd_assoc]

theorem linEnd_of_oLinear (U : UnifPre I D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) (hl : U.OLinear O ιD ιA ιG) (a : O) :
    LinEnd U (ιD.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (ιG.act a) := by
  have := ιG.hom a
  refine ⟨this, fun e => inferInstance, fun e => thickMap_map _ e, fun e => hl.q_lin e a, fun e => ?_⟩
  obtain ⟨t, ht, hi⟩ := hl.i_lin e a
  exact ⟨t, ht, hi⟩

theorem extLam_lam (L : LB G.left) (hL : L.IsLB) :
    ExtLam G (L.pull (pullback.fst G.hom (jK R))) (abelian₂ G L) := by
  refine ⟨LB.isLB_linComb hL _ _, fun κ₂ hκ => ?_⟩
  exact GlobalTheory.LamPull.lbIso_lam_pull (isGrpPullback_pullback G (jK R)) hL (pull_isLB hL _)
    ⟨idIso _, idIso_isGen (pull_isLB hL _)⟩ hκ

theorem exists_model : ∃ (A : PolAV (Sp (FractionRing (PowerSeries ℚ)))) (G : Over (Sp (PowerSeries ℚ))) (_ : GrpObj G)
    (_ : IsCommMonObj G) (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)))
    (U : Unif (maximalIdeal (PowerSeries ℚ)) D A G), LinEnd U.toUnifPre (𝟙 _) (AddMonoidHom.id _) (𝟙 G) ∧
      Module.finrank ℤ D.toPre.X = 1 ∧
      ExtLam G (U.LG.L.pull (pullback.fst G.hom (jK _))) (abelian₂ G U.LG.L) := by
  obtain ⟨A, G, _, _, D, U, -, -, hX, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  exact ⟨A, G, _, _, D, U, linEnd_id _, hX, extLam_lam _ U.LG.isLB⟩

end GlobalTheory.Mum.EndModel

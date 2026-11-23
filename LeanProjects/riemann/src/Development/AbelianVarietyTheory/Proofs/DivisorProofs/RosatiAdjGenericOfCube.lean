import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Definitions.Divisors.LinEndOfOLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosGeneric

theorem linEnd_of_actsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b : D.toPre.P.A ⟶ D.toPre.P.A} {h : D.toPre.X →+ D.toPre.X} {g : G ⟶ G} [IsMonHom g]
    (hg : ActsAs U b h g) : LinEnd U b h g :=
  ⟨inferInstance, fun _ => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map g e, fun e => (hg e).1,
    fun e => (hg e).2⟩

theorem rosatiAdj_generic_of_cube (hcube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L)) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o a g g' hg hg' ag ag'
  have hE := GlobalTheory.Mum.EndModel.endData_of_oAct O D.toPre o a
  have l1 : LinEnd U.toUnifPre (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) g :=
    linEnd_of_actsAs U.toUnifPre ag
  have l2 : LinEnd U.toUnifPre (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) g' := by
    have := linEnd_of_actsAs (h := DistribSMul.toAddMonoidHom D.toPre.X (star (star a))) U.toUnifPre ag'
    simpa only [star_star] using this
  have H := hcube R hR D A G hG U _ _ _ _ hE g g' l1 l2
  obtain ⟨u, hu⟩ := (GlobalTheory.NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB g g' H).1
  have := U.gen_hom
  exact GlobalTheory.EndRosati.rosatiAdj_generic U.toUnifPre (by simp) (by simp) u hu.1

end GlobalTheory.Mum.RosGeneric

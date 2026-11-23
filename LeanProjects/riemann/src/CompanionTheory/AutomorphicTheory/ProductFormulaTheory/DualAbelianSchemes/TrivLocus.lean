import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppTopSurjective
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusB

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem trivLocus_pf : CompanionTheory.ObstructionTrivialLocus.TrivLocus := by
  intro S A Y _ hA hY N hN h0
  obtain ⟨Z, i, hi, hZ⟩ := exists_closed_locTriv_noeth S A Y hA hY N hN
  refine ⟨Z, i, hi, fun T y => ?_⟩
  have e : lift (fst A T) (snd A T ≫ y) = A ◁ y := by ext <;> simp
  rw [← hZ T y, ev, e]
  constructor
  · intro ht p
    exact ⟨⊤, trivial, CubeOpen.triv_pull_pull _ _ (CubeOpen.triv_comp _ rfl ht)⟩
  · intro hloc
    have hpb : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
      IsPullback.of_hasPullback _ _
    have e' : y ≫ lift (1 : Y ⟶ A) (𝟙 Y) = lift (1 : T ⟶ A) (𝟙 T) ≫ A ◁ y := by ext <;> simp
    have hsec : Triv ((N.pull (A ◁ y).left).pull (lift (1 : T ⟶ A) (𝟙 T)).left) :=
      CubeOpen.triv_pull_pull _ _ (CubeOpen.triv_comp y.left (congrArg (·.left) e') h0)
    exact GlobalTheory.exists_gen_of_local_of_section (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left
      (N.pull (A ◁ y).left) (pull_isLB hN _) (congrArg (·.left) (lift_snd (1 : T ⟶ A) (𝟙 T)))
      (GlobalTheory.BaseChangeFns.app_surjective GlobalTheory.globalFns_holds S A hA _ _ T.hom _ _ hpb) hloc hsec

end CompanionTheory.PfDual

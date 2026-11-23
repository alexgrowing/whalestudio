import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
namespace PushCub
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β)

theorem push_one {T : Over S'} : pushHom h T 1 = toUnit _ ≫ η[G] := by
  rw [map_one, Hom.one_def]

theorem face0 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 0 =
    lift (pushHom h (G2 G') 1) (lift (pushHom h (G2 G') (fst G' G')) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face1 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 1 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') 1) (pushHom h (G2 G') (snd G' G'))) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem face2 : lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ faceMap G 2 =
    lift (pushHom h (G2 G') (fst G' G')) (lift (pushHom h (G2 G') (snd G' G')) (pushHom h (G2 G') 1)) := by
  simp only [faceMap, x2, pzero, comp_lift, push_one]
  simp
  rfl

theorem pushPt_lift_cubeTriplePoint_of_isGrpPullback (i : Fin 3) : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫ x3 G i =
    pushHom h (G3 G') (x3 G' i) := by
  fin_cases i <;> simp [x3] <;> rfl

theorem pushPt_lift_cubeQuadruplePoint_of_isGrpPullback (i : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ x4 G i = pushHom h (G4 G') (x4 G' i) := by
  fin_cases i <;> simp [x4] <;> rfl

theorem padd_push (i j : Fin 4) : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2))
    (pushPt h.1.w (x4 G' 3)))) ≫ padd G (x4 G i) (x4 G j) = pushHom h (G4 G') (x4 G' i * x4 G' j) := by
  rw [map_mul, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h i, ← pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h j]
  exact MonObj.comp_mul _ _ _

theorem cubeMapOf_thirdFace_eq_pushPt_lift : (cubeMapOf h).F3 =
    (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left := rfl

theorem sw01 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 1) (lift (x3 G 0) (x3 G 2)) =
    lift (pushHom h (G3 G') (x3 G' 1)) (lift (pushHom h (G3 G') (x3 G' 0)) (pushHom h (G3 G') (x3 G' 2))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem sw12 : lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2))) ≫
    lift (x3 G 0) (lift (x3 G 2) (x3 G 1)) =
    lift (pushHom h (G3 G') (x3 G' 0)) (lift (pushHom h (G3 G') (x3 G' 2)) (pushHom h (G3 G') (x3 G' 1))) := by
  simp only [comp_lift, pushPt_lift_cubeTriplePoint_of_isGrpPullback h]

theorem coc1 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0 * x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc2 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (x4 G 1) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

theorem coc3 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3)) =
    lift (pushHom h (G4 G') (x4 G' 0)) (lift (pushHom h (G4 G') (x4 G' 1 * x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h, padd_push h]

theorem coc4 : lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3)))) ≫ lift (x4 G 1) (lift (x4 G 2) (x4 G 3)) = lift (pushHom h (G4 G') (x4 G' 1)) (lift (pushHom h (G4 G') (x4 G' 2)) (pushHom h (G4 G') (x4 G' 3))) := by
  simp only [comp_lift, pushPt_lift_cubeQuadruplePoint_of_isGrpPullback h]

end PushCub
end GlobalTheory.Mum

namespace GlobalTheory.Mum
open PushCub in

theorem cubicalStr_of_push_val : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  intro S S' G G' _ _ _ _ f β h L t ht i2 c2 i3 c3 i4 c4 hup
  have hv : ∀ {T : Over S'} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (V : Over.mk (T.hom ≫ f) ⟶ G3 G)
      (a b d : T ⟶ G'), V = lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d)) →
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t V.left z J =
        GlobalTheory.CubTransport.thV t z J (pushHom h T a) (pushHom h T b) (pushHom h T d) := by
    rintro T z J V a b d rfl; rfl
  refine ⟨{ t := t, isGen := ht, face := fun i => ?_, cubeSymmetric_swap_first := ?_, cubeSymmetric_swap_last := ?_, cocycle := ?_ }, rfl⟩
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i2 c2 fun z J hJ => ?_
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [← Over.comp_left]
    have C := hup (G2 G') z J hJ
    fin_cases i
    · exact (hv _ 1 (fst G' G') (snd G' G') (face0 h)).trans (C.face _ _)
    · exact (hv _ (fst G' G') 1 (snd G' G') (face1 h)).trans (C.face₂ _ _)
    · exact (hv _ (fst G' G') (snd G' G') 1 (face2 h)).trans (C.face₃ _ _)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s01 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 1) (x3 G' 0) (x3 G' 2) (sw01 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i3 c3 fun z J hJ => ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [cubeMapOf_thirdFace_eq_pushPt_lift h, ← Over.comp_left]
    have C := hup (G3 G') z J hJ
    exact (hv (T := G3 G') _ (x3 G' 0) (x3 G' 1) (x3 G' 2) rfl).trans ((C.s12 _ _ _).trans
      (hv (T := G3 G') _ (x3 G' 0) (x3 G' 2) (x3 G' 1) (sw12 h)).symm)
  · refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB _ i4 c4 fun z J hJ => ?_
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    refine (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)).symm)
    simp only [← Over.comp_left]
    have C := hup (G4 G') z J hJ
    exact (congrArg₂ (· * ·) (hv _ _ _ _ (coc1 h)) (hv _ _ _ _ (coc2 h))).trans ((C.coc _ _ _ _).trans
      (congrArg₂ (· * ·) (hv _ _ _ _ (coc3 h)) (hv _ _ _ _ (coc4 h))).symm)

end GlobalTheory.Mum

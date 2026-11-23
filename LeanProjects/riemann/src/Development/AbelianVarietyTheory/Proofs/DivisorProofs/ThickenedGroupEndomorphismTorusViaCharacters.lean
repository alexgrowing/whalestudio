import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearIffIsOLinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare

theorem q_comm_of_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a : D.P.A ⟶ D.P.A) (F : thickObj R I e G ⟶ thickObj R I e G)
    (hF : F.left ≫ g.pG.left = g.pG.left ≫ a.left) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    have := hF
    simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left] at this
    simpa [Category.assoc] using this
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
    have h1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w g.q
    have h2 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [h1, h2]

theorem torus_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  intro R _ _ I D e G _ _ g a a' _ _ h' u hu h₀ F hF
  have hb : IsMonHom ((Over.pullback (thick R I e)).map a) := inferInstance
  have hq := q_comm_of_isCoordEnd g a F hF.1
  have hd : (g.i ≫ F) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g.isKernel.w, Category.assoc, IsMonHom.one_hom]
  obtain ⟨t, ht⟩ : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X,
      t ≫ g.i = g.i ≫ F :=
    ⟨g.isKernel.lift _ _ hd, g.isKernel.lift_fst _ _ hd⟩
  refine ⟨t, fun χ => unit_ext fun y hy => ?_, ht.symm⟩
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB y
  have hJ : Good D.P.L y J := hJ
  have := g.q_hom
  have v₁ := val_torus g χ hJ t 1
  have v₂ := val_torus g (h' χ) hJ (𝟙 _) 1
  rw [_root_.mul_one, val_unit g _ hJ, _root_.mul_one] at v₁ v₂
  rw [ht] at v₁
  rw [Category.id_comp] at v₂
  have e1 : TorusCoord.im g g.i = 1 := (im_congr g (x' := 1) (by
    rw [g.isKernel.w, MonObj.one_comp, Hom.one_def])).trans (im_one g)
  have v₃ : val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) g.i.left y J = 1 :=
    (val_pull_lift u χ g.pG ((Over.map (thick R I e)).map g.i) hJ).trans
      ((congrArg _ e1).trans (val₂_axis D.P.isAb D.P.isLB a' a u hu h₀ hJ _))
  have v₄ := (hF.2 χ _ g.i.left y J hJ).trans ((congrArg₂ (· * ·) v₂ v₃).trans (_root_.mul_one _))
  refine (gm_res _ y (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans
    ((gm_pull (𝟙 _) t.left y ⊤ trivial _).trans ?_)
  rw [Category.id_comp]
  rw [Over.comp_left] at v₁
  exact v₁.symm.trans v₄

end GlobalTheory.Mum.EndThick

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem exists_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X)
    (hc : ∀ χ, D.c (h' χ) = D.c χ ≫ a') (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) :
    ∃ F, IsCoordEnd g a a' h' u F := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcT : ∀ χ, DegPre.cT D T (h' χ) = DegPre.cT D T χ ≫ a' := fun χ => by
    simp only [DegPre.cT, hc, Category.assoc]
  have key : ∀ χ : D.X, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (g.pG ≫ a) χ) DegPre.gtε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val s r z J = val (g.t (h' χ)) r z J *
          val (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left) r z J := by
    intro χ
    obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (g.pG ≫ a) χ) (ε' := DegPre.gtε)
      (by
        intro U _ f
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _
          (c := (f (padd D.P.A g.pG (DegPre.cT D T (h' χ))).left)⁻¹ * f (DegPre.cT D T (h' χ)).left *
            f g.pG.left * (f (DegPre.zeroT D T).left)⁻¹) ?_
          (prod_ros a' a (DegPre.cT D T χ) g.pG f)).trans ?_
        · rw [Fin.prod_univ_four]
          show f _ ^ (-1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (-1 : ℤ) = _
          simp only [zpow_neg, zpow_one]
          rfl
        · rw [Fin.prod_univ_four]
          show _ = f (padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a)).left ^ (-1 : ℤ) * f (DegPre.cT D T χ).left ^ (1 : ℤ) *
            f (g.pG ≫ a).left ^ (1 : ℤ) * f (DegPre.zeroT D T).left ^ (-1 : ℤ)
          have p1 : padd D.P.A g.pG (DegPre.cT D T χ ≫ a') = (DegPre.cT D T χ ≫ a') * g.pG := mul_comm _ _
          have p2 : padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a) = DegPre.cT D T χ * (g.pG ≫ a) := rfl
          rw [hcT χ, p1, p2]
          simp only [zpow_neg, zpow_one]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
      (LB.mulGen D.P.L _ _ _ _ (g.t (h' χ)) (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.t_gen _) (DVR.pullGen_isGen _ _ _ _ hu _))
    exact ⟨s, hs, fun Z r z J hJ => (hv Z r z J hJ).trans (val_mul hJ _ _ _)⟩

  choose s hs hv using key
  have vv : ∀ χ (y : T.left) J, Good D.P.L y J → val (s χ) (𝟙 _) y J =
      val (g.t (h' χ)) (𝟙 _) y J * val₂ u y J (DegPre.cT D T χ) g.pG := fun χ y J hJ => by
    rw [hv χ _ _ y J hJ, val_pull hJ, Category.id_comp]; rfl
  have hm : ∀ χ χ' (y : T.left) J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J *
      cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) =
        val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J := fun χ χ' y J hJ => by
    have e1 : val (g.t (h' χ + h' χ')) (𝟙 _) y J *
        cubV D.cub y J (DegPre.cT D T χ ≫ a') (DegPre.cT D T χ' ≫ a') g.pG =
          val (g.t (h' χ)) (𝟙 _) y J * val (g.t (h' χ')) (𝟙 _) y J := by
      have := GlobalTheory.TorusCoord.val_t_mul g (𝟙 _) (h' χ) (h' χ') y J hJ
      rw [Category.id_comp] at this
      rw [← hcT, ← hcT]
      exact this
    have e2 := (ros_add D.cub GlobalTheory.globalFns_holds D.P.isAb a' a u hu h₀ hJ (DegPre.cT D T χ) (DegPre.cT D T χ')
      g.pG).1
    have hadd : DegPre.cT D T (χ + χ') = DegPre.cT D T χ * DegPre.cT D T χ' := DVR.cPoint_add D T χ χ'
    rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, map_add, hadd, _root_.mul_assoc, e2, ← _root_.mul_assoc, e1]
    exact mul_mul_mul_comm _ _ _ _
  have hcub : ∀ χ χ' (y : T.left) J, Good D.P.L y J →
      val (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)) (𝟙 _) y J =
        cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) := fun χ χ' y J hJ => by
    exact (val_cub D.cub (𝟙 T) hJ _ _ _).trans (by simp only [Category.id_comp])
  have hmult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)))
      (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' => corr_of_val D.P.isLB fun y J hJ => by
    exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl (hcub χ χ' y J hJ)).trans
      ((hm χ χ' y J hJ).trans (val_mul hJ _ _ _).symm))
  have hzero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L) := corr_of_val D.P.isLB fun y J hJ => by
    have h := hm 0 0 y J hJ
    have c0 : DegPre.cT D T 0 = 1 := cPoint_zero T
    have c1 : cubV D.cub y J (DegPre.cT D T 0) (DegPre.cT D T 0) (g.pG ≫ a) = 1 := by
      rw [c0]
      exact (isCub_cubV D.cub hJ).face 1 _
    rw [c1, add_zero, _root_.mul_one] at h
    exact (mul_eq_left.1 h.symm).trans (val_one _).symm
  let ξ : GtPt D T := ⟨g.pG ≫ a, s, hs, hzero, hmult⟩
  obtain ⟨F, hF⟩ := (GlobalTheory.TorusCoord.toGtPt_bijective g (T := thickObj R I e G)).2 ξ
  have hP := (GlobalTheory.TorusCoord.toGtPt_eq_iff g F ξ).1 hF
  refine ⟨F, hP.1.symm, fun χ Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hP.2 χ) r).symm.trans (hv χ Z r z J hJ))

end GlobalTheory.Mum.EndThick
end

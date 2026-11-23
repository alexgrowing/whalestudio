import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.TorPtEx

theorem exists_gtPt {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (a : Multiplicative D.X →* Γ(T.left, ⊤)ˣ) : ∃ g : GtPt D T, g.b = 1 ∧
      ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val (g.s χ) r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
  have h1 : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T 1 χ) DegPre.gtε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = gm r z ⊤ (a (Multiplicative.ofAdd χ)) := by
    intro χ
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T 1 χ) (ε' := DegPre.gtε) (fun U _ h => by
        have e₁ : padd D.P.A (DegPre.cT D T χ) 1 = DegPre.cT D T χ := _root_.mul_one (DegPre.cT D T χ)
        have e₂ : DegPre.zeroT D T = 1 := rfl
        simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_succ, e₁, e₂])
      (DVR.scaleGen (a (Multiplicative.ofAdd χ)) (LB.oneGen D.P.L)) (DVR.scaleGen_isGen _ _ h1)
    refine ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem PEmpty.elim r) _) (val_one r))).trans
      (_root_.mul_one _)
  choose s hs hv using key
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, hv⟩
  · rw [hv 0 _ _ y J hJ, val_one, ofAdd_zero, map_one, map_one]
  · have c := (val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1).trans
      ((congrArg (cubV D.cub y J _ _) (Category.id_comp (1 : T ⟶ D.P.A))).trans ((isCub_cubV D.cub hJ).face₃ _ _))
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) c)).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ _ y J hJ) (hv _ _ _ y J hJ))).symm)
    rw [_root_.mul_one, ofAdd_add, map_mul, map_mul]; rfl

theorem main : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ a : Multiplicative D.X →* Wˣ, ∃ x : TA V W ⟶ G, U.TorPt a x := by
  intro V _ _ _ hV D A G _ _ U W _ _ _ hW a
  obtain ⟨g, hb, hv⟩ := exists_gtPt D (TA V W)
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom).comp a)
  obtain ⟨x, hx, -⟩ := RedOnto.main V hV D A G U W hW g
  refine ⟨x, fun e Z r xe h => ?_⟩
  obtain ⟨h₁, h₂⟩ := hx e Z r xe h
  refine ⟨hb ▸ h₁, fun χ z J hJ => ?_⟩
  rw [h₂ χ z J hJ, hv χ Z r z J hJ, gm_val r z ⊤ trivial, gs_eq _ z ⊤ trivial]
  rfl

end GlobalTheory.UU.TorPtEx

end

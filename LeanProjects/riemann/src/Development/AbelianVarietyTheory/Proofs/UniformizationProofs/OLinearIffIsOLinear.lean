import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.OLinearMaps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescends
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OLinearCompare

open GlobalTheory.IndefiniteRowSideFullHecke.OLinearMaps GlobalTheory.TorusCoord

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen :=
  isGen_of_gm _ fun _ _ _ _ _ =>
    (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)))

theorem val₂_axis {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) (x : T ⟶ A) : val₂ u z J x 1 = 1 := by
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (𝟙 A) (1 : A ⟶ A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g (𝟙 A) 1 h).trans ?_))
      rw [MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      simp)
    A.hom η[A].left (Over.w η[A]) (globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    (oneGen_isGen L) (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ x.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_pull_lift {b b' : D.P.A ⟶ D.P.A}
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A b' b) rosatiε)) (χ : D.X)
    {T Z : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : Z ⟶ T) {z : Z.left} {J}
    (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ u (lift (toUnit T ≫ D.c χ) p).left) x.left z J =
      val₂ u z J (toUnit Z ≫ D.c χ) (x ≫ p) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_toUnit_assoc]; rfl

end GlobalTheory.OLinearCompare

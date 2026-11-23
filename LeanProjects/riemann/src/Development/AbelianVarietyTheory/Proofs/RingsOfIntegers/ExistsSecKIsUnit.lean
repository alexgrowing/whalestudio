import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericGenerated

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gs_secOfIso {Y Z : Scheme.{0}} {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  refine (gs_res r z inf_le_left hz _).symm.trans ?_
  refine (congrArg (gs r z (A.U a ⊓ B.U b)) (secOfIso_spec t hu hA hB a b)).trans ?_
  unfold isoCand
  refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z inf_le_right hz _))
  rw [gs_unit r z _ hz, map_inv, gm_res r z (divLe a b) hz]

theorem exists_sec_isUnit {X X' Y W Z : Scheme.{0}} {L : LB X} {M : LB X'} (hL : L.IsLB) (hM : M.IsLB)
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (i : W ⟶ X) (ρ : Y ⟶ W) (hρ : ρ ≫ i = g) (k : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin k) (fun _ => i) (fun _ => 1))) (r : Z ⟶ Y) (z : Z)
    (hs : ρ (r z) ∈ nonzeroLocus s) (J : (Z ⟶ X') → M.ι) (hJ : Good M z J) :
    ∃ t : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))), IsUnit (sval t r z J) := by
  obtain ⟨w, hw⟩ : LBIso L (M.pull (gi ≫ p)) :=
    LBIso.chartPull (chartPullSec L g gi e₁)
      (chartPullSame M (fun _ : PUnit => gi ≫ p) (fun _ => p) (fun _ => 1) gi fun _ => rfl) H
  have H₂ := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => g) (fun _ => (k : ℤ))
  have ep : (fun _ : Fin 1 => g ≫ gi ≫ p) = fun _ => p := by
    funext _; rw [← Category.assoc, e₂, Category.id_comp]
  rw [ep] at H₂
  obtain ⟨u, hu⟩ := LBIso.symm H₂
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hI' : Good L z I := hI
  have h1 : (LB.oneGen L (Y := Y)).IsGen := fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => g) (ε' := fun _ => (k : ℤ))
    (fun V _ h => by simp [Fintype.prod_sum_type, hρ])
    (pullMulSec s ρ (LB.oneGen L (Y := Y)) h1)
  have u₁ : IsUnit (sval s (r ≫ ρ) z I) := by
    obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 hs
    have hj' : (r ≫ ρ) z ∈ LB.wchart L (fun _ : Fin k => i) j := hj
    have h₁ : IsUnit (gs (r ≫ ρ) z (LB.wchart L (fun _ : Fin k => i) j) (s.f j)) :=
      (congrArg IsUnit (gs_stalkMap (r ≫ ρ) z _ hj' _)).mpr (hu.map _)
    exact isUnit_of_mul_isUnit_right ((congrArg IsUnit (sec_trans s (r ≫ ρ) z hj' (hI'.mem _ _))).mp h₁)
  have u₂ : IsUnit (sval s' r z I) := by
    rw [hs' Z r z I hI', sval_pullMulSec s ρ _ _ r z hI']
    exact u₁.mul (Units.isUnit _)
  refine ⟨secOfIso s' hu (linComb_isLB M hM _ _) (linComb_isLB L hL _ _), ?_⟩
  have e := gs_secOfIso u s' hu (linComb_isLB M hM _ _) (linComb_isLB L hL _ _)
    (fun _ => J (r ≫ p)) (fun _ => I (r ≫ g)) r z
    ⟨hJ.mem (fun _ : Fin 1 => p) r, hI'.mem (fun _ : Fin 1 => g) r⟩
  exact (congrArg IsUnit e).mpr ((Units.isUnit _).mul u₂)

theorem exists_secK_isUnit : AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 4 ≤ k → ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (jK R)) (z : Z) (J), Geo.Tor.Good U.LG.L z J → ∃ s : U.SecK k, IsUnit (Geo.Tor.sval s r z J) := by
  intro hA R _ _ I D A G _ _ U k hk Z r z J hJ
  obtain ⟨N, s, hcov⟩ := (hA _ A k hk).1 ⊤ (isAffineOpen_top _)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : pullback G.hom (jK R) ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme,
      ρ ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = U.gen.hom.left :=
    ⟨IsOpenImmersion.lift _ U.gen.hom.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ρ (r z) ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  exact exists_sec_isUnit A.isLB U.LG.isLB U.gen.hom.left U.gen.inv.left
    (congrArg (fun q => q.left) U.gen.inv_hom_id) (congrArg (fun q => q.left) U.gen.hom_inv_id) _ U.ext _ ρ hρ k
    (s i) r z hi J hJ

end GlobalTheory.GenericGenerated

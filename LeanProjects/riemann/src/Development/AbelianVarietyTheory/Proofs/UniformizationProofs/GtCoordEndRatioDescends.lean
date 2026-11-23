import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

open CoordCompare TorusCoord in

theorem gtCoord_end_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  intro R _ _ I D e G _ _ g a aB h t ha ht hi hq χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hp : (Over.map (thick R I e)).map a ≫ g.pG = g.pG ≫ aB := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g.q.left = g.q.left ≫ ((Over.pullback (thick R I e)).map aB).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map aB).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ aB.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D.Oφ g.pG χ k =
      g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.Oφ aB χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g.pG χ k).trans
      ((congrArg (D.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g.pG aB χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D.Oφ g.pG (h χ) k =
      g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D.Oφ · (h χ) k) (Category.comp_id g.pG).symm).trans
      ((WeightPf.Oφ_comp g.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫
      Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · exact congrArg₂ (· ^ ·) (congrArg f (e₂ k)) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
      · exact congrArg (fun ψ => f ψ ^ Oinvε k) (e₁ k))
    (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t (h χ))) (LB.pullGen D.P.L _ _ (g.t χ) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (g.t_gen _)) (pullGen_isGen _ _ _ _ (g.t_gen χ) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      val u r z J = (val (g.t (h χ)) r z J)⁻¹ * val (g.t χ) (r ≫ a.left) z J := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (Geo.Tor.val_inv _ _) (Geo.Tor.val_pull hJ _ _ _)))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
      rw [← Over.w g.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
    let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
    let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hr)
    have hτa : b ≫ a = ((τ ≫ t) ≫ g.i) * (b' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g (h χ) (Z := Z') hJ τ b'
    have v₂ := val_torus g χ (Z := Z') hJ (τ ≫ t) (b' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D.X χ) = gm τ.left z ⊤ (charUnit _ D.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

end GlobalTheory

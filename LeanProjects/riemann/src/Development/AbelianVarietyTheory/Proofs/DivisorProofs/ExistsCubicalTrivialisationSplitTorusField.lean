import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubTriv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorusCubTriv

open GlobalTheory GlobalTheory.UU GlobalTheory.EvenGenTorus TorusCube

theorem exists_cubTriv : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  intro k _ hk G₀ _ _ X _ _ _ P₀ i hi
  letI := hk.toField
  haveI := hi
  haveI : IsAffine (splitTorus (Sp k) X).left := isAffine_of_isAffineHom (splitTorus (Sp k) X).hom
  haveI := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus k X
  obtain ⟨τ, hτ⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb P₀.L.isLB (K := PUnit) (fun _ => i.left) (fun _ => 1))
  have e1 : (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left ≫ i.left = (1 : splitTorus (Sp k) X ⟶ G₀).left := by
    rw [← Over.comp_left, MonObj.one_comp]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two, e1]))
    (LB.mulGen _ _ _ _ _ τ (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => i.left) (fun _ => 1) τ
      (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have v : ∀ (T : Over (Sp k)) (x : T ⟶ splitTorus (Sp k) X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val τ x.left z J * (val τ (1 : T ⟶ splitTorus (Sp k) X).left z J)⁻¹ := by
    intro T x z J hJ
    rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩⟩
  have a := cube k X G₀ i P₀.L P₀.c τ hτ T x y u z J hJ
  simp only [v T _ z J hJ]
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

end GlobalTheory.Mum.TorusCubTriv

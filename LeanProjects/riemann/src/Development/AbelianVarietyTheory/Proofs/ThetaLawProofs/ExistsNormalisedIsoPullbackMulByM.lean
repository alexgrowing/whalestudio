import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa

theorem exists_zpowGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z J => map_zpow _ _ _⟩
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (congrArg _ (map_zpow _ _ _).symm))
  rw [gen_trans ht (𝟙 Y) y hj hj', mul_zpow]
  congr 1
  simp only [trF, zpow_mul, Finset.prod_zpow]

theorem exists_normalised_mulPull : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ), ∃ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen ∧ ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) := by
  intro laws R _ _ x m
  have hL := x.P.isLB
  obtain ⟨α, hα⟩ := laws.mulPull _ x.P m
  obtain ⟨ρ, hρ, hρv⟩ := exists_zpowGen (φ := fun _ : PUnit => eSec x.P.A) (ε := fun _ => 1) x.rig x.rig_gen
    (1 - (m : ℤ) ^ 2)
  have e₁ : eSec x.P.A ≫ (Out.mulA x.P.A m).left = eSec x.P.A := by
    have : η[x.P.A] ≫ Out.mulA x.P.A m = η[x.P.A] := by
      have h1 : η[x.P.A] = (1 : 𝟙_ (Over (Sp R)) ⟶ x.P.A) := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [MonObj.comp_pow, Category.comp_id, h1, one_pow]
    exact congrArg (·.left) this
  have e₂ : eSec x.P.A ≫ (toUnit x.P.A).left = 𝟙 _ := by
    have : η[x.P.A] ≫ toUnit x.P.A = 𝟙 _ := toUnit_unique _ _
    exact congrArg (·.left) this
  obtain ⟨mu, hmu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left])
    (ε' := ![1, -(m : ℤ) ^ 2]) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen x.P.L _ _ _ _ (LB.invGen x.P.L _ _ α) (LB.pullGen x.P.L _ _
      (LB.mulGen x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (eSec x.P.A)) ρ) (toUnit x.P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ hα) (DVR.pullGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) hρ) _))
  refine ⟨mu, hmu, fun p J hJ => ?_⟩
  rw [hv _ _ p J hJ, val_mul hJ, val_inv, val_pull hJ, val_mul hJ, val_pull hJ, hρv, e₂, Category.id_comp,
    inv_mul_cancel_left]

end GlobalTheory.KeyKa
end

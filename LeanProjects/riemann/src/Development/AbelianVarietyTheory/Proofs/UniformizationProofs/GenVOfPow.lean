import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.FrameVal
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.CoefUnit

theorem genV_of_pow : AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (w₁ : Frm D.toPre F 1 p.g.b), w₁.IsGen → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ n) (4 * n ^ 2) 4), κ.IsGen → (∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J ^ (4 * n ^ 2) * val κ p.g.b.left z J = (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J) * rigV D.toPre (TF (R := V) F).hom z J) ^ 4) → GenV hϖ hv w₁ ((Q p.y : ℚ) / (n : ℚ) ^ 2) := by
  intro V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv n hn p w hw κ hκ H
  have hL := D.toPre.P.isLB
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  have hmy : cP D.toPre (TWM.TO hϖ hv) p.y = m ^ n := TWM.liftO_unique hϖ hv _ _ (by
    rw [comp_cP, cPoint_y, ← hm]; exact (map_pow (preHom (TWM.ιS hϖ hv)) m n).symm)
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local D.toPre.P.L hL (TWM.lineφO hϖ hv m) (DegPre.lineε 1)
  have hl : ∀ i, DegPre.lineφ D.toPre F p.g.b i = (TWM.ιS hϖ hv).left ≫ TWM.lineφO hϖ hv m i := by
    intro i; fin_cases i
    · show (DegPre.zeroF D.toPre F).left = (TWM.ιS hϖ hv).left ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
    · show p.g.b.left = (TWM.ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
  obtain ⟨x, hx0, hx⟩ := TWM.exists_ratio hL w hw (LB.pullGen D.toPre.P.L _ _ t₀ (TWM.ιS hϖ hv).left)
    (pullGen_isGen _ _ _ _ ht₀ _) (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hl])
  have hx' : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val =
      cst (R := V) F z x * (val t₀ (TWM.ιS hϖ hv).left z J).val := fun z J hJ => by
    have e := hx _ (𝟙 _) z J hJ
    rw [val_pull hJ] at e
    exact e
  refine ⟨TWM.lineφO hϖ hv m, hl, t₀, ht₀, x, ?_, hx'⟩
  obtain ⟨e, c, he, hc, hce⟩ := SectionScalarValuation.exists_val_genHasVal (hQ p.y)
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have q₁ : (TWM.TO hϖ hv).hom ≫ (D.toPre.c p.y).left = (m ^ n).left := hmy ▸ rfl
      have q₂ : m.left ≫ (𝟙 D.toPre.P.A ^ n).left = (m ^ n).left :=
        congrArg (·.left) ((map_pow (preHom m) (𝟙 D.toPre.P.A) n).trans (congrArg (· ^ n) (Category.comp_id m)))
      have q₃ : m.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left :=
        congrArg (·.left) (MonObj.comp_one (M := D.toPre.P.A) m)
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_unique (_ : PUnit → U), Fintype.prod_unique (_ : PUnit → U), q, q₁, Fin.prod_univ_two,
        Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        TWM.lineφO, DegPre.lineε, q₂, q₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen _ _ _ _ _ (GeneratorPullback.powGen _ _ _ t₀ (4 * n ^ 2)) (LB.pullGen _ _ _ κ m.left))
    (mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ hκ _))
    (GeneratorPullback.powGen _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ e (TWM.TO hϖ hv).hom)
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TWM.TO hϖ hv).hom)) 4)
    (DVR.powGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ he _)
      (DVR.pullGen_isGen _ _ _ _ D.toPre.rig_gen _)) _)
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := eu z J hJ
  rw [val_mul hJ, RatioVal.val_powGen, RatioVal.val_powGen, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ,
    Over.w (TWM.ιS hϖ hv), ← Over.comp_left, hm] at a
  have b := congrArg Units.val (H z J hJ)
  have d : (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J)).val =
      cstH z (algebraMap (FractionRing V) F c) * (val e (TF (R := V) F).hom z J).val :=
    (hce _ (jFK (R := V) F) z J hJ).trans (congrArg (· * _) (RatioVal.gs_scal _ z c))
  have key : x ^ (4 * n ^ 2) * u = algebraMap (FractionRing V) F c ^ 4 := by
    apply cstH_inj (R := V) z
    apply ((val e (TF (R := V) F).hom z J * rigV D.toPre (TF (R := V) F).hom z J) ^ 4).isUnit.mul_right_cancel
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, d, hx' z J hJ, cst_eq, rigV, map_mul, map_pow, mul_pow] at a b ⊢
    linear_combination b - cstH z x ^ (4 * n ^ 2) * a
  have k := congrArg v key
  obtain ⟨q, hq⟩ := TWM.wt_coe_of_ne (v := v) hx0
  rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow, hu, hv _ _ hc, hq] at k
  have k' : (4 * n ^ 2) • q + 0 = 4 • ((Q p.y : ℤ) : ℚ) := by exact_mod_cast k
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [hq, WithTop.coe_inj, eq_div_iff (pow_ne_zero 2 hn0)]
  simp only [nsmul_eq_mul] at k'
  push_cast at k'
  linarith

end GlobalTheory.UT.FrameVal
end

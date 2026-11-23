import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
namespace GlobalTheory.Mum.Two.Mix
open GlobalTheory.UT.MixedConv

theorem val_mixed_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  intro R _ _ D₁ D₂ F _ _ b h g g' hg j j' w w' χ δ u hu f f' y y' hy hy' z J hJ
  have h₁ : Good D₁.P.L z (rl J) := (isPart_inl D₁.P.L D₂.P.L).good hJ
  have h₂ : Good D₂.P.L z (rr J) := (isPart_inr D₁.P.L D₂.P.L).good hJ
  have c₂ : val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J) =
      th D₁ z (rl J) (cP D₁ _ (h χ)) (cP D₁ _ δ) g.b := by
    refine (val_cub D₁.cub g.b h₁ _ _ _).trans ?_
    rw [comp_cP, comp_cP, Category.comp_id]
  have c₃ := gt_mul (𝟙 (TF (R := R) F)) h₁ g (h χ) δ
  have c₄ := hy z (rr J) h₂
  have c₅ := hy' z (rl J) h₁
  have c₆ : g.b.left ≫ b.left = g'.b.left := (congrArg (fun q => q.left) hg.1).symm
  have c₉ := hg.2 χ u hu z J hJ
  rw [Category.id_comp, Over.id_left] at c₃
  rw [c₉, CoefBasic.cst_eq] at c₄
  rw [CoefBasic.cst_eq] at c₅
  rw [c₂, c₆, CoefBasic.cst_eq, map_mul, eq_comm, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_eq_iff_eq_mul]
  have c₇ := congrArg Units.val c₃
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c₄ c₅ c₇ ⊢
  have c₈ := congrArg₂ (· * ·) c₄ c₅
  linear_combination c₈ - sval f (Over.Hom.left g'.b) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J).val *
    (val w (𝟙 _) z (rr J)).val * (val w' (𝟙 _) z (rl J)).val * c₇

end GlobalTheory.Mum.Two.Mix

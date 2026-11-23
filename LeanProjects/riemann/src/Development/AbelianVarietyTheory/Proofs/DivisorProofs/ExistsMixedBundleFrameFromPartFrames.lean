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

noncomputable section

namespace GlobalTheory.Mum.Two.Mix

theorem exists_frame_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) (j j' : ℕ) (g : GtPtF D₁ F) (b' : TF (R := R) F ⟶ D₂.P.A), b' = g.b ≫ b → ∀ (w : Frm D₂ F j b') (w' : Frm D₁ F j' g.b), w.IsGen → w'.IsGen → ∃ τ : LB.Gen (LB.LinComb (JN D₁ D₂) (fun i => g.b.left ≫ mixφ D₁ D₂ b α i) (MixedConv.mixε j j')), τ.IsGen ∧ ∀ z J, Good (JN D₁ D₂) z J → val τ (𝟙 _) z J = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s α) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹ := by
  intro R _ _ D₁ D₂ F _ _ b α j j' g b' hb w w' hw hw'
  subst hb
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  let ρ₁ : LB.Gen (LB.LinComb D₁.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₁.P.A) (fun _ => 1)) :=
    LB.pullGen D₁.P.L (fun _ : PUnit.{1} => eSec D₁.P.A) (fun _ => 1) D₁.rig (TF (R := R) F).hom
  have hρ₁ : ρ₁.IsGen := DVR.pullGen_isGen _ _ _ _ D₁.rig_gen _
  let ρ₂ : LB.Gen (LB.LinComb D₂.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₂.P.A) (fun _ => 1)) :=
    LB.pullGen D₂.P.L (fun _ : PUnit.{1} => eSec D₂.P.A) (fun _ => 1) D₂.rig (TF (R := R) F).hom
  have hρ₂ : ρ₂.IsGen := DVR.pullGen_isGen _ _ _ _ D₂.rig_gen _
  let t := LB.mulGen (JN D₁ D₂) _ _ _ _
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₂.gen (GeneratorPullback.powGen D₂.P.L _ _ ρ₂ j)) (p₁.gen (GeneratorPullback.powGen D₁.P.L _ _ ρ₁ j')))
    (LB.invGen (JN D₁ D₂) _ _ (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₁.gen (g.s α))
      (LB.mulGen (JN D₁ D₂) _ _ _ _ (p₂.gen w) (p₁.gen w'))))
  have ht : t.IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂.gen_isGen (DVR.powGen_isGen _ _ _ _ hρ₂ _))
        (p₁.gen_isGen (DVR.powGen_isGen _ _ _ _ hρ₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₁.gen_isGen (g.isGen α))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (p₂.gen_isGen hw) (p₁.gen_isGen hw'))))
  obtain ⟨τ, hτ, hv⟩ := exists_gen (jn_isLB D₁ D₂) (φ' := fun i => g.b.left ≫ mixφ D₁ D₂ b α i)
    (ε' := MixedConv.mixε j j') (fun U _ h => by
      have q₁ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₂.P.A) i ≫ coprod.inr) ^
          ((j : ℤ) * (fun _ => (1 : ℤ)) i) = h ((1 : TF (R := R) F ⟶ D₂.P.A).left ≫ coprod.inr) ^ (j : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have q₂ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D₁.P.A) i ≫ coprod.inl) ^
          ((j' : ℤ) * (fun _ => (1 : ℤ)) i) = h ((1 : TF (R := R) F ⟶ D₁.P.A).left ≫ coprod.inl) ^ (j' : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have q₃ := prod_gt g.b α (fun f => h (f ≫ coprod.inl))
      have q₄ := CoefBasic.prod_line j (g.b ≫ b) (fun f => h (f ≫ coprod.inr))
      have q₅ := CoefBasic.prod_line j' g.b (fun f => h (f ≫ coprod.inl))
      have q₆ := prod_neg (fun i => h (Sum.elim (fun k => DegPre.gtφ D₁ F g.b α k ≫ coprod.inl)
        (Sum.elim (fun k => DegPre.lineφ D₂ F (g.b ≫ b) k ≫ coprod.inr) (fun k => DegPre.lineφ D₁ F g.b k ≫ coprod.inl)) i))
        (Sum.elim DegPre.gtε (Sum.elim (DegPre.lineε j) (DegPre.lineε j')))
        (DVR.prod_sum₂ (U := U) _ q₃ (DVR.prod_sum₂ (U := U) _ q₄ q₅))
      have q₇a : ∏ i : PUnit.{1}, h (g.b.left ≫ mixφ D₁ D₂ b α (.inl i)) ^ MixedConv.mixε j j' (.inl i) =
          h ((g.b ≫ b).left ≫ coprod.inr) ^ (j : ℤ) := by
        rw [Fintype.prod_unique]
        show h (g.b.left ≫ b.left ≫ coprod.inr) ^ (j : ℤ) = _
        rw [Over.comp_left, Category.assoc]
      have q₇b : ∏ i : Fin 4, h (g.b.left ≫ mixφ D₁ D₂ b α (.inr i)) ^ MixedConv.mixε j j' (.inr i) =
          ∏ i, (fun f => h (f ≫ coprod.inl)) (g.b.left ≫ D₁.famφB α i) ^ DegPre.famε j' i :=
        Finset.prod_congr rfl fun i _ => by
          show h (g.b.left ≫ D₁.famφB α i ≫ coprod.inl) ^ DegPre.famε j' i = _
          rw [← Category.assoc]
      have q₇c := MixedConv.prod_comp D₁ g.b α j' (fun f => h (f ≫ coprod.inl))
      refine Eq.trans (DVR.prod_sum₂ (U := U) _ (DVR.prod_sum₂ (U := U) _ q₁ q₂) q₆)
        (Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ q₇a (q₇b.trans q₇c)).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module) t ht
  refine ⟨τ, hτ, fun z J hJ => (hv _ _ z J hJ).trans ?_⟩
  have g₁ := p₁.good hJ
  have g₂ := p₂.good hJ
  have e₂ : val (GeneratorPullback.powGen D₂.P.L _ _ ρ₂ j) (𝟙 _) z (rr J) = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j :=
    (map_pow _ _ _).trans (congrArg (· ^ j) ((val_pull g₂ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  have e₁ : val (GeneratorPullback.powGen D₁.P.L _ _ ρ₁ j') (𝟙 _) z (rl J) = rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' :=
    (map_pow _ _ _).trans (congrArg (· ^ j') ((val_pull g₁ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  rw [val_mul hJ, val_mul hJ, val_inv, val_mul hJ, val_mul hJ, p₂.val_gen _ _ _ hJ, p₁.val_gen _ _ _ hJ,
    p₁.val_gen _ _ _ hJ, p₂.val_gen _ _ _ hJ, p₁.val_gen _ _ _ hJ]
  rw [← e₁, ← e₂]

end GlobalTheory.Mum.Two.Mix

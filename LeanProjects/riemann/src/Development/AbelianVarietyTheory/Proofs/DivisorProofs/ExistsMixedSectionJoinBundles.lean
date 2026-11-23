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

theorem prod_mix_hom {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X)
    (j j' : ℕ) {U : Type} [CommGroup U] (h : (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U) :
    ∏ i, h (mixφ D₁ D₂ b α i) ^ MixedConv.mixε j j' i = h (b.left ≫ coprod.inr) ^ (j : ℤ) *
      (h (Over.Hom.left (𝟙 D₁.P.A) ≫ coprod.inl) ^ ((j' : ℤ) - 1) * h ((cP D₁ D₁.P.A α * 𝟙 D₁.P.A).left ≫ coprod.inl) *
        (h ((cP D₁ D₁.P.A α).left ≫ coprod.inl))⁻¹ * h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl)) :=
  DVR.prod_sum₂ (K := PUnit.{1}) (K' := Fin 4) (U := U) _ (Fintype.prod_unique _)
    (MixedConv.prod_comp D₁ (𝟙 _) α j' (fun q => h (q ≫ coprod.inl)))

theorem exists_mix_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (j j' : ℕ) (χ : D₂.X) (χ' β α : D₁.X), χ' + β = α → ∀ (u : LB.Gen (CmpLB D₁ D₂ b χ' χ)), u.IsGen → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' β), ∃ n : LB.Sec (LB.LinComb (JN D₁ D₂) (mixφ D₁ D₂ b α) (MixedConv.mixε j j')), ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J), Good (JN D₁ D₂) z J → sval n r z J = sval f (r ≫ b.left) z (rr J) * sval f' r z (rl J) * (val u r z J * val (MixedConv.cubB D₁ χ' β) r z (rl J)).val := by
  intro R _ _ D₁ D₂ b j j' χ χ' β α hα u hu f f'
  subst hα
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  obtain ⟨t, ht⟩ := exists_sec (jn_isLB D₁ D₂) (φ' := mixφ D₁ D₂ b (χ' + β)) (ε' := MixedConv.mixε j j')
    (fun U _ h => by
      have q₁ := prod_cub (cP D₁ D₁.P.A χ') (cP D₁ D₁.P.A β) (𝟙 D₁.P.A) (fun q => h (q ≫ coprod.inl))
      have q₂ := MixedConv.prod_comp D₂ b χ j (fun q => h (q ≫ coprod.inr))
      have q₃ := MixedConv.prod_comp D₁ (𝟙 _) β j' (fun q => h (q ≫ coprod.inl))
      have q₄ := prod_mix_hom D₁ D₂ b (χ' + β) j j' h
      have q₅ := MixedConv.prod_coord D₁ (𝟙 _) χ' (fun q => h (q ≫ coprod.inl))
      have q₆ := MixedConv.prod_coord_inv D₂ b χ (fun q => h (q ≫ coprod.inr))
      rw [DVR.cPoint_add] at q₄
      simp only [Over.id_left, Category.id_comp] at q₃ q₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := (Fin 4 ⊕ Fin 4) ⊕ thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₂ q₃)
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₅ q₆) q₁)) (Eq.trans ?_ q₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left, Category.id_comp]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec (p₂.sec (H1.SectionArithmetic.pullSec f b.left)) (p₁.sec f'))
      (Geo.Tor.genSec (LB.mulGen (JN D₁ D₂) _ _ _ _ u (p₁.gen (MixedConv.cubB D₁ χ' β)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (p₁.gen_isGen (MixedConv.cubB_isGen D₁ χ' β)))))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  exact (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((p₂.sval_sec _ _ z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (p₂.good hJ))) (p₁.sval_sec _ _ z hJ)))
    ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (p₁.val_gen _ _ z hJ)))))))

end GlobalTheory.Mum.Two.Mix

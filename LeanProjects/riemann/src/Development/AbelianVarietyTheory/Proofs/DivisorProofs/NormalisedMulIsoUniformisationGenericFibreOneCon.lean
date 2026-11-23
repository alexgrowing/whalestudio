import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GenericMove

theorem move_one_const : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (N : ℕ) (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![𝟙 A.A.left, (mulA A.A N).left] ![(N : ℤ) ^ 2, -1])), α.IsGen → ∀ (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (mulA G N).left] ![(N : ℤ) ^ 2, -1])), β.IsGen → ∃ c : FractionRing V, c ≠ 0 ∧ ∀ (r : (TF (R := V) (FractionRing V)).left ⟶ ((Over.pullback (jK V)).obj G).left), r ≫ ((Over.pullback (jK V)).obj G).hom = 𝟙 _ → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (val β (r ≫ pullback.fst G.hom (jK V)) z JG).val = GlobalTheory.UT.cst (FractionRing V) z c * (GlobalTheory.TorsFrameInt.wv w₀ r z JG JA ^ ((N : ℤ) ^ 2) * (GlobalTheory.TorsFrameInt.wv w₀ (r ≫ (mulA ((Over.pullback (jK V)).obj G) N).left) z JG JA)⁻¹ * val α (r ≫ U.gen.hom.left) z JA).val := by
  intro V _ _ I D A G _ _ U w₀ hw₀ N α hα β hβ
  haveI := U.gen_hom
  have h₁ : ∀ k : Fin 2, (![𝟙 ((Over.pullback (jK V)).obj G).left,
      (mulA ((Over.pullback (jK V)).obj G) N).left] : Fin 2 → _) k ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ (![𝟙 G.left, (mulA G N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact GlobalTheory.TorsFrameInt.mulA_comm (isGrpPullback_pullback G (jK V)) N
  have hmA : mulA ((Over.pullback (jK V)).obj G) N ≫ U.gen.hom = U.gen.hom ≫ mulA A.A N := by
    rw [mulA, mulA, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have h₂ : ∀ k : Fin 2, (![𝟙 ((Over.pullback (jK V)).obj G).left,
      (mulA ((Over.pullback (jK V)).obj G) N).left] : Fin 2 → _) k ≫ U.gen.hom.left =
      U.gen.hom.left ≫ (![𝟙 A.A.left, (mulA A.A N).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact congrArg (fun q => q.left) hmA
  obtain ⟨a, ha, hav⟩ := GlobalTheory.TorsFrameInt.exists_move U.LG.isLB A.isLB w₀ hw₀ _ _ _ ![(N : ℤ) ^ 2, -1] h₁ h₂ β hβ
  obtain ⟨ρ, hρ⟩ := exists_ratio A.isLB rfl a (LB.pullGen A.L _ _ α U.gen.hom.left) ha
    (pullGen_isGen _ _ _ _ hα _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.BoxExpansion.unit_const GlobalTheory.abelianSchemeLaws_all.1.globalFns A U.gen ρ
  refine ⟨c, hc0, fun r hr z JA JG hJA hJG => ?_⟩
  have hg : (gm r z ⊤ ρ).val = GlobalTheory.UT.cst (FractionRing V) z c := by
    rw [← gs_unit r z ⊤ trivial ρ, hc]
    exact (gs_pull r ((Over.pullback (jK V)).obj G).hom z ⊤ trivial _).trans (by rw [hr]; rfl)
  have e := hav _ r z JG JA hJG hJA
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at e
  rw [e, hρ _ r z JA hJA, val_pull hJA, zpow_neg_one, mul_left_comm, Units.val_mul, hg]

end GlobalTheory.GenericMove

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDataFirstFactorAdjointPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegDataSecondFactorInclProjAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsUniformisedBySumStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem prod_main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂), ∃ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂)) (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (q₁ : D.toPre.X →+ D₁.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSemiAbelian (G₁ ⊗ G₂) ∧ i₁ ≫ p₁ = 𝟙 _ ∧ i₂ ≫ p₂ = 𝟙 _ ∧ (∀ y, q₁ (j₁ y) = y) ∧ (∀ y, q₂ (j₂ y) = y) ∧ Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ ∧ Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ ∧ LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) ∧ GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂
  obtain ⟨D, p₁, p₂, q₁, q₂, pD⟩ := GlobalTheory.T.exists_product_degenerationData_sum R (maximalIdeal R) D₁ D₂
  obtain ⟨A, a₁, a₂, pA, -⟩ := GlobalTheory.T.exists_product_principallyPolarised_abelianScheme _ A₁ A₂
  obtain ⟨U, hg₁, hg₂, H⟩ := GlobalTheory.T.product_uniformised_groups_uniformised_by_sum R hR D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ pD pA
  haveI := pD.lim
  let e := AddEquiv.ofBijective (q₁.prod q₂) pD.xsum
  let i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A := lift (𝟙 _) (toUnit _ ≫ η[D₂.toPre.P.A]) ≫ inv (lift p₁ p₂)
  let i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A := lift (toUnit _ ≫ η[D₁.toPre.P.A]) (𝟙 _) ≫ inv (lift p₁ p₂)
  let j₁ : D₁.toPre.X →+ D.toPre.X := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
  let j₂ : D₂.toPre.X →+ D.toPre.X := e.symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _)
  have hinv₁ : inv (lift p₁ p₂) ≫ p₁ = fst _ _ := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hinv₂ : inv (lift p₁ p₂) ≫ p₂ = snd _ _ := by
    rw [IsIso.inv_comp_eq, lift_snd]
  have hi₁₁ : i₁ ≫ p₁ = 𝟙 _ := by simp only [i₁, Category.assoc, hinv₁, lift_fst]
  have hi₁₂ : i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] := by simp only [i₁, Category.assoc, hinv₂, lift_snd]
  have hi₂₁ : i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] := by simp only [i₂, Category.assoc, hinv₁, lift_fst]
  have hi₂₂ : i₂ ≫ p₂ = 𝟙 _ := by simp only [i₂, Category.assoc, hinv₂, lift_snd]
  have he : ∀ z, e (e.symm z) = z := e.apply_symm_apply
  have hj₁₁ : ∀ y, q₁ (j₁ y) = y := fun y => congrArg Prod.fst (he (y, 0))
  have hj₁₂ : ∀ y, q₂ (j₁ y) = 0 := fun y => congrArg Prod.snd (he (y, 0))
  have hj₂₁ : ∀ y, q₁ (j₂ y) = 0 := fun y => congrArg Prod.fst (he (0, y))
  have hj₂₂ : ∀ y, q₂ (j₂ y) = y := fun y => congrArg Prod.snd (he (0, y))
  obtain ⟨l₁, l₂, l₃, l₄⟩ := H i₁ i₂ j₁ j₂ hi₁₁ hi₁₂ hi₂₁ hi₂₂ hj₁₁ hj₁₂ hj₂₁ hj₂₂
  exact ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, GlobalTheory.T.isSemiAbelian_tensor_over_scheme _ G₁ G₂ hG₁ hG₂, hi₁₁, hi₂₂, hj₁₁, hj₂₂,
    GlobalTheory.T.productData_firstFactor_adjointPair R _ D D₁ D₂ p₁ p₂ q₁ q₂ pD i₁ j₁ hi₁₁ hi₁₂ hj₁₁ hj₁₂,
    GlobalTheory.T.productDegData_secondFactor_incl_proj_adjoint R _ D D₁ D₂ p₁ p₂ q₁ q₂ pD i₂ j₂ hi₂₁ hi₂₂ hj₂₁ hj₂₂, l₁, l₂, l₃, l₄, hg₁, hg₂⟩

end GlobalTheory.MumProd

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSndOfIsProdUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfTorusHomOfZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomLiftOneId

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProdUnifSum

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) ∧ ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) := by
  intro R _ _ _ hB D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  obtain ⟨U, hU⟩ := GlobalTheory.T.uniformisation_product_of_uniformisedGroups R hB D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  refine ⟨U, GlobalTheory.MumProd.gAdj_prod_fst R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    GlobalTheory.MumProd.SndAdj.gAdj_snd_of_isProdUnif R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hU,
    fun i₁ i₂ j₁ j₂ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨?_, hU.linHom_fst j₁ h5 h6, ?_, hU.linHom_snd j₂ h7 h8⟩⟩
  · exact GlobalTheory.MumProd.IsProdUnif.linHom_inl R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ h1 h2
  · exact GlobalTheory.MumProd.linHom_lift_one_id R _ D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre D A U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₂ h3 h4

end GlobalTheory.MumProdUnifSum

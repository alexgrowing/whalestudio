import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  first | exact @GlobalTheory.ArtinGlue.exists_principal_glue | exact GlobalTheory.ArtinGlue.exists_principal_glue | (intros; apply GlobalTheory.ArtinGlue.exists_principal_glue <;> assumption)

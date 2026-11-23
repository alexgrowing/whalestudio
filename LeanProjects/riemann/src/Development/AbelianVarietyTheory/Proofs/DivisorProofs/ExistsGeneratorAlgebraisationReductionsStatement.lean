import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorAlgebraisationReductions
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_algebraisation_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : LB X.left), N.IsLB → ∀ s : ∀ e (i : N.ι), Γ((Y e).left, b e ⁻¹ᵁ N.U i)ˣ, (∀ e z i i', b e z ∈ N.U i → b e z ∈ N.U i' → gm (𝟙 _) z _ (s e i) = gm (b e) z _ (N.g i i') * gm (𝟙 _) z _ (s e i')) → (∀ e z i, b e z ∈ N.U i → gm (β e) z _ (s (e + 1) i) = gm (𝟙 _) z _ (s e i)) → ∃ t : LB.Gen N, t.IsGen := by
  first | exact @GlobalTheory.FormalAlg.exists_isGen_of_reductions | exact GlobalTheory.FormalAlg.exists_isGen_of_reductions | (intros; apply GlobalTheory.FormalAlg.exists_isGen_of_reductions <;> assumption)

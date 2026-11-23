import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsuppMapDomainEqZeroAtFilteredStage
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage : ∀ (Λ : Type 1) [AddCommGroup Λ] (J : Type) [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q), (∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x) → (∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y) → ∀ j (x : P.obj j →₀ Λ), Finsupp.mapDomain (ι j) x = 0 → ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  first | (exact @GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (exact GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (intros; apply GlobalTheory.finsupp_mapDomain_eq_zero_at_stage  <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FieldIntersectionLinearDegreeOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_intersection_linear_degree_one : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K), (∀ a : K, a = k₀) → ∀ (J : IFamily F ι), IsFieldIntersection J → ∀ (S : Set (MRingOver F ι)), (∀ f ∈ S, IsMultiHomog f fun _ => 1) → ∀ r : ℕ, IsProjVarF (Ideal.span S) r → J (Ideal.span S) r (fun _ _ => 1) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.linear_subspace_degree_one | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.linear_subspace_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.linear_subspace_degree_one <;> assumption)

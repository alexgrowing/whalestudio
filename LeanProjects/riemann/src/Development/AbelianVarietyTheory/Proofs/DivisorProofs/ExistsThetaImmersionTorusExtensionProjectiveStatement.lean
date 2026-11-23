import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_immersion_torus_extension_projective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (S : Finset D.toPre.X) (k₁ : ℕ), ∀ k ≥ k₁, ∃ (N : ℕ) (α : Fin (N + 1) → D.toPre.X) (b : ∀ i, D.toPre.SecB k (α i)) (τ : Fin (N + 1) → SecK D.toPre.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), (∀ i, α i ∈ S ∧ IsTermOf Y (b i) (τ i)) ∧ IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
  first | exact @GlobalTheory.Mum.ThetaImm.exists_immersion | exact GlobalTheory.Mum.ThetaImm.exists_immersion | (intros; apply GlobalTheory.Mum.ThetaImm.exists_immersion <;> assumption)

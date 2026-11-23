import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InConeOfMonomialMultiple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inCone_of_monomial_multiple : ∀ {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) {m : ℕ} (t : Fin m → R) (γ δ : Fin m → LinearMap.BilinForm ℤ Dg.X) (N : ℕ), 0 < N → (∀ i, γ i = (N : ℤ) • δ i) → (∀ i y z, δ i y z = δ i z y) → (∀ i, δ i ≠ 0) → IsMonomial Dg t γ → InCone Dg δ := by
  first | exact @GlobalTheory.GenFan.inCone_of_isMonomial_smul | exact GlobalTheory.GenFan.inCone_of_isMonomial_smul | (intros; apply GlobalTheory.GenFan.inCone_of_isMonomial_smul <;> assumption)

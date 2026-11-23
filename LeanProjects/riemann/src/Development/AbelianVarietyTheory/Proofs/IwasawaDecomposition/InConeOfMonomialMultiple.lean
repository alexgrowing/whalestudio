import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormAtIdOfIsMonomial

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem inCone_of_isMonomial_smul {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) {m : ℕ} (t : Fin m → R)
    (γ δ : Fin m → LinearMap.BilinForm ℤ Dg.X) (N : ℕ) (_hN : 0 < N) (hγ : ∀ i, γ i = (N : ℤ) • δ i)
    (hs : ∀ i y z, δ i y z = δ i z y) (_hne : ∀ i, δ i ≠ 0) (hm : IsMonomial Dg t γ) : InCone Dg δ := by
  intro W _ _ _ hW ϖ hϖ f be hbe hf
  have hsγ : ∀ i y z, γ i y z = γ i z y := fun i y z => by
    rw [hγ i, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, hs i y z]
  obtain ⟨c, hc, e⟩ := StepCheck.inCone_of_isMonomial hsγ hm W hW ϖ hϖ f be hbe hf
  refine ⟨fun i => c i * N, fun i => mul_nonneg (hc i) N.cast_nonneg, ?_⟩
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  simp [toReal, hγ i, smul_eq_mul, mul_assoc]

end GlobalTheory.GenFan

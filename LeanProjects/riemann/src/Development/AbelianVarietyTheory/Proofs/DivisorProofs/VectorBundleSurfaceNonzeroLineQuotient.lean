import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.Proof.Div.vector_bundle_surface_nonzero_line_quotient

theorem exists_hom_isVB_one_ne_zero : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]
    [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E (r + 1) →
      ∃ (L : T.Modules) (φ : E ⟶ L), IsVB L 1 ∧ φ ≠ 0 := by
  intro k _ T _ _ hT E r hE
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hT.isProjOver).2
  have := hE.dual.isFiniteQC
  obtain ⟨n, m, ψ, hψ⟩ := (hA.eventually_exists_epi_sigma (dual E)).exists
  have hM : IsVB (toMod (lbZPow A (-n))) 1 := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  have hne : ¬ IsZero (dual E) := fun hz => by
    haveI : Nonempty T := IsIntegral.nonempty
    have := hE.dual.rank_unique (isVB_zero_iff.2 hz)
    omega
  obtain ⟨i, hi⟩ : ∃ i, Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : ψ = 0 := Sigma.hom_ext _ _ fun i => by simp [h i]
    subst h0
    exact hne (IsZero.of_epi_zero (∐ fun _ : Fin m => toMod (lbZPow A (-n))) (dual E))
  set χ := Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ with hχ
  refine ⟨dual (toMod (lbZPow A (-n))), cartierDualToBidual E ≫ dualMap χ, hM.dual, fun h0 => hi ?_⟩
  have := hE.isIso_toBidual_of_local_frames
  have := hE.dual.isIso_toBidual_of_local_frames
  have h1 : dualMap χ = 0 := by
    rw [← cancel_epi (cartierDualToBidual E), h0, comp_zero]
  have h2 : χ ≫ cartierDualToBidual (dual E) = 0 := by
    rw [toBidual_naturality_dualSheafTranspose, h1, dualMap_zero, comp_zero]
  rw [← cancel_mono (cartierDualToBidual (dual E)), h2, zero_comp]

end GlobalTheory.Proof.Div.vector_bundle_surface_nonzero_line_quotient

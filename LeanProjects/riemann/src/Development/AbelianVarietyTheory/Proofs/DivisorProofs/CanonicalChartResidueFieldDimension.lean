import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddTrdegCompletionPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedSymmIntBilinFormsEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem canon_residue_dim : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → ((residue (ChartRing k m e)).comp C.b).EssFiniteType ∧ (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra; ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim) := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hC
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringKrullDim_add_trdeg_completion_polynomial c.F hC.L.W (ChartRing k m e) hC.L.b hC.L.ft (Fin C.m ⊕ Fin hC.N) hC.ψ hC.compl hC.ψ_loc
    C.b hC.base
  refine ⟨h1, ?_⟩
  obtain ⟨a, t, ha, ht, hat⟩ := hC.L.dim
  obtain ⟨a', t', ha', ht', hat'⟩ := h2 a t ha ht
  have hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]
    simp [Nat.card_sum]
  have hma : a' = m + e := by
    rw [hdimR] at ha'
    exact_mod_cast ha'.symm
  have hcard : Fintype.card (Fin C.m ⊕ Fin hC.N) = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) hC.L.D.X *
      Module.finrank (𝓞 E) hC.L.D.X := by
    rw [← GlobalTheory.T.finrank_balancedSymmIntBilinForms_eq H hC.L.D.X, Module.finrank_eq_card_basis hC.ε]
  have hr : Module.finrank (𝓞 E) C.P.D.toPre.X = Module.finrank (𝓞 E) hC.L.D.X := hC.e.finrank_eq
  have hp := hC.hp
  have hq := hC.hq
  rw [hr] at hp hq
  have key : a' + t' = Dw.dim := by
    rw [hat', hat, hcard, Datum.dim, Datum.dim, ← hp, ← hq]
    ring
  rw [ht', ← hma]
  exact_mod_cast key

end GlobalTheory.UCanon

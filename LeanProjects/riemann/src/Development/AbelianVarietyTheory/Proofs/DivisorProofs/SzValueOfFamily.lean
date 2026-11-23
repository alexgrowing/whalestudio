import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOpsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrallyClosedPadicIntegralSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuationStatement

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_value_of_family (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) (Ω : ℂ)
    (hN : 0 < N) (hact : ActBij act) (hf : IsFam act w f) (hq : ∀ i, QAll (Sz l lam r) N (f i))
    (hj : Sz l lam 0 (jT τ₀)) (hΩ : Ω ^ 12 = DD τ₀) (i : ι) :
    Sz l lam r (f i τ₀ / Ω ^ w) := by
  refine GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt l lam r _ fun q hrq => ?_
  obtain ⟨c, hc0, hc, hc'⟩ := GlobalTheory.T.exists_algebraic_of_rational_valuation l lam q
  obtain ⟨R, hR, hcl⟩ := GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring l lam
  obtain ⟨hconst, hmono, -, hmul, -⟩ := GlobalTheory.T.qExpansionValuationBound_ring_closure l lam N hN
  have hfam : IsFam act w fun i τ => c * f i τ := (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.1 w c f hf
  have hq' : ∀ i, QAll (· ∈ R) N fun τ => c * f i τ := fun i => by
    obtain ⟨a, ha, ha'⟩ := hmono _ 0 _ (by linarith) (hmul _ _ _ _ (hconst _ c hc) (hq i))
    exact ⟨a, ha, fun n => (hR _).2 (ha' n)⟩
  have hjR : IsIntegral R (jT τ₀) :=
    isIntegral_algebraMap (R := R) (A := ℂ) (x := ⟨jT τ₀, (hR _).2 hj⟩)
  have h0 : Sz l lam 0 (c * f i τ₀ / Ω ^ w) :=
    (hR _).1 (hcl _ (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N _ R τ₀ Ω hN hact hfam hq' hjR hΩ i))
  have h1 := (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 _ _ _ _ hc' h0
  have e : c⁻¹ * (c * f i τ₀ / Ω ^ w) = f i τ₀ / Ω ^ w := by
    rw [mul_div_assoc, inv_mul_cancel_left₀ hc0]
  rwa [add_zero, e] at h1

end GlobalTheory.QFam

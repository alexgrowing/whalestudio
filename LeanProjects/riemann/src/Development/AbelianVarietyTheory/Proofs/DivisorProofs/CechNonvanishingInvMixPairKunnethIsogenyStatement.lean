import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_pair_of_nv | exact GlobalTheory.AmpleGen.nv_mix_pair_of_nv | (intros; apply GlobalTheory.AmpleGen.nv_mix_pair_of_nv <;> assumption)

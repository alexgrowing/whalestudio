import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoefficientValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHilbertLatticeContainsAndCoordinateSizeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassTorsionQExpansionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.SizeGL

theorem main : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ)) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hf s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hlM hML hLsz hNsz hρ hρ0 hlM' hMy hy α
  have hA := GlobalTheory.WpFam.Act.rightActions N
  have hS := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hTw : HasLevel N (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) :=
    GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL
  obtain ⟨hmem, hsz⟩ := GlobalTheory.T.twistedHilbertLattice_contains_and_coordinate_size l lam F N (M * l ^ b) L α ρ₀ hL.2 hML hLsz hNsz
  have hx : M' • vmul y α = 0 := by rw [← hA.2.2.2.2.2.1, hMy]; exact (hA.2.2.2.2.1 0 α).mpr rfl
  have hx0 : vmul y α ≠ 0 := fun h => hy ((hA.2.2.2.2.1 y α).mp h)
  obtain ⟨hQ, -⟩ := GlobalTheory.T.weierstrassTorsion_qExpansion_integral l lam N M' (vmul y α) hlM' hx hx0
  have hQρ : QAll (Sz l lam ρ) N (wB N (vmul y α)) := by
    obtain ⟨a, ha, hp⟩ := hQ
    exact ⟨a, ha, fun n => hS.2.2.2.1 0 ρ _ hρ0 (hp n)⟩
  exact GlobalTheory.T.hilbertEisenstein_coefficient_valuation_bound hE F hf s N _ hs hN hTw z hz l lam κ (wB N (vmul y α)) M b e ρ₀ ρ he hze hlM hmem hsz hρ hQρ

end GlobalTheory.HilbFam.SizeGL

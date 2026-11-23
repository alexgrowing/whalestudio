import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharacterEntrySumEisensteinProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DropConst
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product : ∀ (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K], 1 ≤ m → 0 < N → ¬ p ∣ N → 3 ≤ k → ∀ (ψ : DirichletCharacter K (p ^ m)), ψ.IsPrimitive → ∀ (ζ : K), IsPrimitiveRoot ζ (N * p ^ m) → ∀ (a₀ b₀ t : ℤ), (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ (i j : ℕ), ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) * (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i * coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) = if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  first | exact @GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum | exact GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum | (intros; apply GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum <;> assumption)

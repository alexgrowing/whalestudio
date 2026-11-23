import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerStructureExists

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem exists_dividedPowers_map_quotient {S : Type} [CommRing S] (hS : TF S) (I J : Ideal S)
    (hI : PdI I)
    (hJ : ∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) :
    ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  obtain ⟨δ₀, -, hδ₀⟩ := exists_dividedPowers hS I hI
  have hsub : DividedPowers.IsSubDPIdeal δ₀ (J ⊓ I) :=
    { isSubideal := inf_le_right
      dpow_mem := fun n hn j hj =>
        ⟨hJ j hj.2 hj.1 n hn _ (δ₀.factorial_mul_dpow_eq_pow hj.2),
          δ₀.dpow_mem hn hj.2⟩ }
  refine ⟨DividedPowers.Quotient.dividedPowers δ₀ hsub, rfl, fun k x y hx e => ?_⟩
  rw [DividedPowers.Quotient.dpow_apply δ₀ hsub hx]
  exact congrArg _ (hδ₀ k x y hx e)

end GlobalTheory.CompanionTheory.PdTF

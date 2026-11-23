import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalVector_value_unitaryRankOne_gindikinKarpelevich : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (u : GU σ n), (∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j) →
    φ (y⁻¹ * u) = if Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 then 1
      else α k ^ (-ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) *
        (q : ℂ) ^ (ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) := by
  first | exact @GlobalTheory.GKUnitaryRankOne.value_rankOne | exact GlobalTheory.GKUnitaryRankOne.value_rankOne | (intros; apply GlobalTheory.GKUnitaryRankOne.value_rankOne <;> assumption)

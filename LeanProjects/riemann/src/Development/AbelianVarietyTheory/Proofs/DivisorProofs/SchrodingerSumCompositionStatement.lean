import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSumComposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_sum_composition : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b c a' b' c' : (κ → R) × (κ → R)),
    (∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a φ = GlobalTheory.WeilM.schr ψ b (GlobalTheory.WeilM.schr ψ c φ)) →
    (∀ φ : (κ → R) → ℂ, GlobalTheory.WeilM.schr ψ a' φ = GlobalTheory.WeilM.schr ψ b' (GlobalTheory.WeilM.schr ψ c' φ)) →
    ∀ Φ : (κ ⊕ κ → R) → ℂ,
      GlobalTheory.WeilM.schr ψ (Sum.elim a.1 a'.1, Sum.elim a.2 (-a'.2)) Φ =
        GlobalTheory.WeilM.schr ψ (Sum.elim b.1 0, Sum.elim b.2 0)
          (GlobalTheory.WeilM.schr ψ (Sum.elim 0 b'.1, Sum.elim 0 (-b'.2))
            (GlobalTheory.WeilM.schr ψ (Sum.elim c.1 c'.1, Sum.elim c.2 (-c'.2)) Φ)) := by
  first | exact @GlobalTheory.schr_block_factor | exact GlobalTheory.schr_block_factor | (intros; apply GlobalTheory.schr_block_factor <;> assumption)

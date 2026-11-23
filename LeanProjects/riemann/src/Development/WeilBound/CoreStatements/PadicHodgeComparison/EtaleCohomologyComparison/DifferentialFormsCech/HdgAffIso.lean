import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om

theorem hdg_iso (h : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q] (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] HodgeC q a j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q]
      [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ) (x : HT.Hdg p a (a + j)),
      e q a j (HT.pullH u hu a (a + j) x) = pullC u hu a j (e p a j x)) : type_of% @h := @h

end CrystallineSemistableComparison.Om

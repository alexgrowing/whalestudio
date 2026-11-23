import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Vert.Flag

theorem exists_local_lift_gr : ∀ {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N)
    (i : Fin N) (U : X.Opens) (e : Γ(fl.gr i, U)) (y : X), y ∈ U →
    ∃ (W : X.Opens) (hW : W ≤ U) (t : Γ(fl.F i.succ, W)),
      y ∈ W ∧ (fl.π i).app W t = Twist.resM _ hW e := by
  intro X M N fl i U e y hy
  obtain ⟨W, hW, hy', t, ht⟩ := VB.exists_app_eq_of_epi (fl.π i) e hy
  exact ⟨W, hW, t, hy', ht⟩

end GlobalTheory.Vert.Flag

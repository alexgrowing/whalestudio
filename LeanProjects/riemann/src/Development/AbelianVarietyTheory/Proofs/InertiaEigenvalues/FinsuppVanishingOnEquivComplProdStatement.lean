import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_finsupp_compl_prod_eq : ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  first | exact @GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | exact GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | (intros; apply GlobalTheory.finsupp_vanishing_on_equiv_compl_prod <;> assumption)

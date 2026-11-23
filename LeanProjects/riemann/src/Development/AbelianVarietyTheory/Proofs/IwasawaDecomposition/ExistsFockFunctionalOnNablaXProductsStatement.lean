import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFockFunctionalOnNablaXProducts
import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fock_functional_on_nablaX_products : ∀ (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ),
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) := by
  first | exact @GlobalTheory.FockMinorFunctional.fock_functional_nablaX | exact GlobalTheory.FockMinorFunctional.fock_functional_nablaX | (intros; apply GlobalTheory.FockMinorFunctional.fock_functional_nablaX <;> assumption)

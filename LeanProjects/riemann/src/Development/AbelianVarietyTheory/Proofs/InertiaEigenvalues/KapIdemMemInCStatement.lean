import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KapIdemMemInC
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kap_mem_inC_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL), IsActC act → IsIdempotentElem e → (∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) → ∀ k, kap o e k ∈ inC K.1 := by
  first | exact @GlobalTheory.Cyc.Decomp.kap_idem_mem_inC | exact GlobalTheory.Cyc.Decomp.kap_idem_mem_inC | (intros; apply GlobalTheory.Cyc.Decomp.kap_idem_mem_inC <;> assumption)

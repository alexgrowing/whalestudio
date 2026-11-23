import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffBasisCoordsMemCyclotomicLevelOfPowe
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n] (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l), (∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a) → φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ‖(c : PadicComplex l)‖ < 1 → (c : PadicComplex l) ∈ inC (Ks K m) → (∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) → ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  first | exact @GlobalTheory.Cyc.Decomp.Coord.coord | exact GlobalTheory.Cyc.Decomp.Coord.coord | (intros; apply GlobalTheory.Cyc.Decomp.Coord.coord <;> assumption)

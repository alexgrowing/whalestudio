import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c ∈ BQ LA _ hI) ∧ (∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ quotientCocycles LA _ hI, CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c' ∈ BQ LA' _ hI') := by
  first | exact @GlobalTheory.TateFin.tate_pairing_nondegenerate | exact GlobalTheory.TateFin.tate_pairing_nondegenerate | (intros; apply GlobalTheory.TateFin.tate_pairing_nondegenerate <;> assumption)

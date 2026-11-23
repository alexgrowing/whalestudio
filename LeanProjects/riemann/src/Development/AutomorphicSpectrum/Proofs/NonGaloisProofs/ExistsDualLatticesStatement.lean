import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_lattices : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), cycIntCore ((D.loc l).PD K) ∧ ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 ((D.loc l).PD K) LA LA' P ∧ IsDualLat1 ((D.loc l).PD K) LA' LA P.flip := by
  first | exact @GlobalTheory.CompanionTheory.LocDual.Lat.dual_lattices_exist | exact GlobalTheory.CompanionTheory.LocDual.Lat.dual_lattices_exist | (intros; apply GlobalTheory.CompanionTheory.LocDual.Lat.dual_lattices_exist <;> assumption)

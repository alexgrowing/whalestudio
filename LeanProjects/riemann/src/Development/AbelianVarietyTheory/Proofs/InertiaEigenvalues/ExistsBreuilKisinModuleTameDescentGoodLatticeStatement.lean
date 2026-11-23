import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), (∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H) → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∃ Pk : Pack a ϖ η H T, Pk.D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) := by
  first | exact @GlobalTheory.BKGal.exists_pack_isOfType | exact GlobalTheory.BKGal.exists_pack_isOfType | (intros; apply GlobalTheory.BKGal.exists_pack_isOfType <;> assumption)

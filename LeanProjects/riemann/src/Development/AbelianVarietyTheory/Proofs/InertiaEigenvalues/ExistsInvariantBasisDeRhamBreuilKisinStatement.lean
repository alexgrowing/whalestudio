import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  first | exact @GlobalTheory.BKLim.InvBasis.exists_invariant_basis | exact GlobalTheory.BKLim.InvBasis.exists_invariant_basis | (intros; apply GlobalTheory.BKLim.InvBasis.exists_invariant_basis <;> assumption)

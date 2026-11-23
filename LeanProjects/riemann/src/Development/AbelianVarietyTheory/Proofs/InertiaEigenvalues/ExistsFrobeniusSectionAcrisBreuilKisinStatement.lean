import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_section_acris_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → ∃ (k : ℕ) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) ∧ (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) ∧ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) ^ N • (Q * (A.map fun s => ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))))) = ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • ((A.map fun s => ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a s)) * Q.map (phiA l)) := by
  first | exact @GlobalTheory.CrisSec.phiSection | exact GlobalTheory.CrisSec.phiSection | (intros; apply GlobalTheory.CrisSec.phiSection <;> assumption)

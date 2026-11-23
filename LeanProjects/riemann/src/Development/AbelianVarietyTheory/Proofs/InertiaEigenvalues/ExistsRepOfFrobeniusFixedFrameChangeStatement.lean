import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_of_frobeniusFixed_frame_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w e : Fin r → n → ℤ) (U : Fin r → GL n P.R.BdR) (A : GL n P.R.B), IsRat r ρ → (∀ (m : Fin r) (g : ↥(GK K)), matD P ρ m g * (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) → (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) → (∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (e m j)) * (W : Matrix n n P.R.BdR)) → ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + e m j) ∧ (AdmSt P ρ' → AdmSt P ρ) := by
  first | exact @GlobalTheory.PMon.exists_rep_of_fixed_frame_change | exact GlobalTheory.PMon.exists_rep_of_fixed_frame_change | (intros; apply GlobalTheory.PMon.exists_rep_of_fixed_frame_change <;> assumption)

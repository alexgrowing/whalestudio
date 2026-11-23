import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltration
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  first | exact @GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | exact GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | (intros; apply GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPairingDstDcrisFrobeniusFixed
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  first | exact @GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one | exact GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one | (intros; apply GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one <;> assumption)

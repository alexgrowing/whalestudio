import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainSymplecticPreimage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_symplectic_preimage : ∀ {g : ℕ} (M : Submodule ℤ (Fl g)) (γ : Sp g) (D : Set (Fl g)), IsAddFundamentalDomain (latAct M γ) D volume → IsAddFundamentalDomain M ((fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D) volume := by
  first | exact @GlobalTheory.TorsionForm.isAddFundamentalDomain_preimage_latAct | exact GlobalTheory.TorsionForm.isAddFundamentalDomain_preimage_latAct | (intros; apply GlobalTheory.TorsionForm.isAddFundamentalDomain_preimage_latAct <;> assumption)

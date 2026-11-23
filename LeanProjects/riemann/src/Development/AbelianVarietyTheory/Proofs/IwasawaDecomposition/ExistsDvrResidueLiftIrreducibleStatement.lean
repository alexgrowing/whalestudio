import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueLiftIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open IsLocalRing GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_residue_lift_irreducible : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ {L : Type} [Field L] (v : ResidueField W →+* L), v.Finite → v.FormallyUnramified → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (τ : L →+* ResidueField V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (f ϖ)) ∧ ∀ w : W, τ (v (residue W w)) = residue V (f w) := by
  first | exact @GlobalTheory.exists_unramified_ext_residue | exact GlobalTheory.exists_unramified_ext_residue | (intros; apply GlobalTheory.exists_unramified_ext_residue <;> assumption)

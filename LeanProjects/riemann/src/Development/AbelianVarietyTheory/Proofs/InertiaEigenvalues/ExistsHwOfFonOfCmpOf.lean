import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithfulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctorStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_hwOf_fonOf_cmpOf : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  intro L A hT hW
  have key : ∀ (l : ℕ) [Fact l.Prime], ∃ H : LocHW l (L l), ∃ F : LocFon l (L l) (A l) H,
      Nonempty (LocCmpT l (L l) (A l) H F) := fun l _ =>
    GlobalTheory.T.exists_local_wach_functor l (L l) (A l) (hT l) (GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful l (L l) (A l)) (hW l)
  choose H F hC using key
  exact ⟨fun l _ => H l, fun l _ => F l, ⟨fun l _ => (hC l).some⟩⟩

end GlobalTheory.HWL

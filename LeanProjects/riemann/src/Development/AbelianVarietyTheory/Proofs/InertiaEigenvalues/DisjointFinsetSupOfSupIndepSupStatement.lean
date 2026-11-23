import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSup
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' : ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → Disjoint (F.sup G) (F.sup B) := by
  first | exact @GlobalTheory.disjoint_finset_sup_of_supIndep_sup | exact GlobalTheory.disjoint_finset_sup_of_supIndep_sup | (intros; apply GlobalTheory.disjoint_finset_sup_of_supIndep_sup <;> assumption)

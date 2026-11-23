import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalExtensionWithSimpleRoot
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_local_extension_with_simple_root : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω] (u : A →+* Ω) (p : Polynomial A) (α : Ω), RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic → (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω), a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  first | exact @GlobalTheory.MonicRootExtension.exists_extension | exact GlobalTheory.MonicRootExtension.exists_extension | (intros; apply GlobalTheory.MonicRootExtension.exists_extension <;> assumption)

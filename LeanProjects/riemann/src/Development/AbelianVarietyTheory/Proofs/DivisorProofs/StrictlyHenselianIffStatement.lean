import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime], q.comap (algebraMap R A) = maximalIdeal R → ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔ (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  first | exact @GlobalTheory.StrictHensel.strictlyHenselian_iff | exact GlobalTheory.StrictHensel.strictlyHenselian_iff | (intros; apply GlobalTheory.StrictHensel.strictlyHenselian_iff <;> assumption)

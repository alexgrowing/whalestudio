import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_residue_comp_etale_henselian : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B], Function.Bijective (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  first | exact @GlobalTheory.EtaleHensel.bijective_residue_comp | exact GlobalTheory.EtaleHensel.bijective_residue_comp | (intros; apply GlobalTheory.EtaleHensel.bijective_residue_comp <;> assumption)

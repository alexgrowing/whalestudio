import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) → ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ, (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) → t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | exact GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | (intros; apply GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub <;> assumption)

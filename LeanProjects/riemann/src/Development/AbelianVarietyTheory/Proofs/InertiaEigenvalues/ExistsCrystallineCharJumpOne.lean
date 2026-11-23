import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbeddingStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LTChar

theorem exists_crystalline_char_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀
  haveI := (P.PD K).finK₀
  have hn : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  obtain ⟨x, hxu, hxφ, hx1, hx2, hxj⟩ := GlobalTheory.T.exists_cyclotomic_period_local_prime l P AI hT K _ hn
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unramified_character_of_eigen_unit l P K x hxu (GlobalTheory.T.galois_periodRatio_mem_unramified_alt l P AI hT K x hxu hxφ hx1 hx2 hxj)
  have hcont := GlobalTheory.T.continuous_galois_character_of_bcris_unit_fil_one l P AI hT K x hxu hx1 hx2 c hc
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.exists_continuous_integralUnitChar_of_char l K LL τ₀ c hcont
  exact ⟨χ, hχc, GlobalTheory.T.crystalline_character_jump_one_at_embedding l P AI hT K LL hA τ₀ x hxu hxφ hx1 hx2 hxj c hc _ hχc hχ⟩

end GlobalTheory.LTChar

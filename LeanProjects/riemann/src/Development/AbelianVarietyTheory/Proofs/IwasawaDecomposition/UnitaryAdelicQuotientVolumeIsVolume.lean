import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetPosFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotientStatement

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volIs_trueVol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  apply trueVol_spec
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure F E cm I τ cd W hτ hW
  obtain ⟨⟨𝓕, h𝓕⟩, hall⟩ := GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq F E cm.sig W.rank W.gram μ hμ.1
  have hcm := cmData_isCMExt_and_gram_isHermND F E cm
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E cm.sig hcm.1 W.rank W.gram (hcm.2 W) μ hμ.1 𝓕 h𝓕
  have hne : μ 𝓕 ≠ 0 := (hall 𝓕 𝓕 h𝓕 h𝓕).2
  refine ⟨(μ 𝓕).toReal, ENNReal.toReal_pos hne hfin.ne, ⟨μ, hμ⟩, ?_⟩
  intro μ' hμ'
  have e : μ = μ' := GlobalTheory.Mem.VolUnique.volMeas_unique F E cm I τ cd W hτ hW μ μ' hμ hμ'
  subst e
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓕' h' => ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  exact (hall 𝓕' 𝓕 h' h𝓕).1

end GlobalTheory.Mem.Vol

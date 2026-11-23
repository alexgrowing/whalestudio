import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.WeilM

open scoped Classical

theorem integrable_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (f : SInf F κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    @Integrable _ _ _ _ (borel _) (pureA F f g) μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI := Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  haveI hρ : Measure.IsAddHaarMeasure ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) :=
    (GlobalTheory.WeilAdm.HaarSplit.splitE F κ).isAddHaarMeasure_map _ (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ)
      (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AF F) :=
    (Homeomorph.mk (GlobalTheory.WeilAdm.HaarSplit.splitE F κ).toEquiv (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ)
      (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)).toMeasurableEquiv
  have hgi : Integrable g ν := hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have hρi : Integrable (pureA F f g) ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) := by
    have e : ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) = (volume.prod ν).map em := rfl
    rw [e, integrable_map_equiv em]
    have e2 : pureA F f g ∘ em = fun p => f p.1 * g p.2 := funext fun p =>
      GlobalTheory.WeilAdm.HaarSplit.pureA_splitE F κ f g p
    rw [e2]
    exact (f.integrable (μ := volume)).mul_prod hgi
  rw [Measure.isAddLeftInvariant_eq_smul μ ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ))]
  exact hρi.smul_measure ENNReal.coe_ne_top

theorem schA_integrable : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ μY : Measure (κ → AF F), μY.IsAddHaarMeasure → ∀ φ ∈ schA F κ, Integrable φ μY := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  exact integrable_finsetSum' _ fun i _ => integrable_pureA μ hμ (f i) (hg i)

end GlobalTheory.WeilM

end

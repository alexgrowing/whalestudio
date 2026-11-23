import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem integrable_mixedModel_partialFourier_integrand {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] {r : ℕ} (μ : Measure F) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hψ : IsLocallyConstant (fun x => ψ x))
    (f : Gl r F → ℂ) (hf : IsTest f) (Y : Gl r F) :
    Integrable (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1))
      (Measure.pi fun _ : Fin r => μ) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : Continuous (fun b : Fin r → F => f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1)) := by
    refine Continuous.mul ?_ ?_
    · exact hf.1.continuous.comp (by fun_prop)
    · exact hψ.continuous.comp (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun Z : Gl r F => Z.2.1) '' tsupport f) := hf.2.isCompact.image (by fun_prop)
  refine HasCompactSupport.intro hK ?_
  intro b hb
  have : (Y.1, b, Y.2.2.1, Y.2.2.2) ∉ tsupport f := fun h => hb ⟨_, h, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.ptrB_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  intro F E _ _ _ _ hU r M ψ hψ c f f' hf hf'
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  have hlc : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  funext Y
  have h1 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f hf Y
  have h2 := WeilMix.integrable_mixedModel_partialFourier_integrand M.μF ψ hlc f' hf' Y
  simp only [WeilMix.ptrB, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul c) h2, integral_const_mul]

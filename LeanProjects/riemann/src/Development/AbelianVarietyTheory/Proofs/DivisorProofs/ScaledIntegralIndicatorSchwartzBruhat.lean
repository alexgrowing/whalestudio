import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.EvAdm

theorem indicator_sub_mem_scaledInt_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ a r ha
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  set U : Set (κ → FiniteAdeleRing (𝓞 F) F) := (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) with hU
  have hUo : IsOpen U := isOpen_scaledInt a
  have hUc : IsClosed U := AddSubgroup.isClosed_of_isOpen _ hUo
  have hsub : U ⊆ (fun z : κ → FiniteAdeleRing (𝓞 F) F => fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i) ''
      GlobalTheory.SchANonzero.intPts F κ := by
    intro z hz
    refine ⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩
    · have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _
      exact h1 ▸ (mem_scaledInt.mp hz i v)
    · funext i
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) a * (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) = z i
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  have hUk : IsCompact U :=
    ((GlobalTheory.SchANonzero.isCompact_intPts F κ).image
      (continuous_pi fun i => continuous_const.mul (continuous_apply i))).of_isClosed_subset hUc hsub
  set S : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} with hS
  have hSe : S = (fun y => y - r) ⁻¹' U := rfl
  have hcont : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r := continuous_id.sub continuous_const
  have hSo : IsOpen S := hSe ▸ hUo.preimage hcont
  have hSc : IsClosed S := hSe ▸ hUc.preimage hcont
  have hSk : IsCompact S := by
    have : S = (fun y => y + r) '' U := by
      ext y
      simp only [hSe, Set.mem_preimage, Set.mem_image]
      exact ⟨fun h => ⟨y - r, h, sub_add_cancel y r⟩, fun ⟨x, hx, hxy⟩ => by rw [← hxy, add_sub_cancel_right]; exact hx⟩
    rw [this]
    exact hUk.image (continuous_id.add continuous_const)
  refine ⟨?_, HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ S
  · exact ⟨S, hSo, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

end GlobalTheory.EvAdm

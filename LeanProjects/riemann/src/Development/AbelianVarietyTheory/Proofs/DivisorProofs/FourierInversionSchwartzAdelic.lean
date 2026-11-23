import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NullOfFiniteCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaAdelicHaarEqMapProductMeasureStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.TamFourier

theorem fourier_inversion_tamagawa : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ → ∀ Φ ∈ schA F κ, ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x) := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ Φ hΦ x
  have hFT : ∀ H ∈ schA F κ, (fun y : κ → AF F => ∫ z, H z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ :=
    GlobalTheory.T.adelicFourier_mem_schwartz_totallyReal F hF ψ hψ κ μ hμ.1
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : GlobalTheory.SWQ.Ctx ψ lam ν a := ⟨hF, hψ, hlam, hν, fun _ => by norm_num [a]⟩
  have hμeq := GlobalTheory.T.tamagawa_adelicHaar_eq_map_product_measure F κ N e ν hν μ hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := GlobalTheory.PoissonReindex.reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  have key : ∀ (H : (κ → AF F) → ℂ) (y' : Fin N → AF F),
      ∫ z, H z * ψ (z ⬝ᵥ T y') ∂μ = GlobalTheory.SWQ.Fo ψ ν a (fun u => H (T u)) y' := by
    intro H y'
    have hm : μ = Measure.map Tm (GlobalTheory.SWQ.muV N ν) := hμeq
    rw [hm, integral_map_equiv]
    simp only [GlobalTheory.SWQ.Fo, hTm, a, GlobalTheory.PoissonReindex.Bd_half, T, GlobalTheory.PoissonReindex.dot_reidx]
  set G : (κ → AF F) → ℂ := fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have hG' : (fun u => G (T u)) = GlobalTheory.SWQ.Fo ψ ν a Φ' := funext fun u => key Φ u
  have hGG : (fun u => (∫ z, G z * ψ (z ⬝ᵥ T u) ∂μ)) = GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact funext fun u => key G u
  have hΦs : Φ' ∈ schA F (Fin N) := GlobalTheory.PoissonReindex.mem_schA_reidx e hΦ
  have hGs : G ∈ schA F κ := hFT Φ hΦ
  have hGGs : (fun y : κ → AF F => ∫ z, G z * ψ (z ⬝ᵥ y) ∂μ) ∈ schA F κ := hFT G hGs
  have hD1 : GlobalTheory.SWQ.Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦs
  have hD2 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a Φ') := by
    rw [← hG']
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGs)
  have hD3 : GlobalTheory.SWQ.Decay (GlobalTheory.SWQ.Fo ψ ν a (GlobalTheory.SWQ.Fo ψ ν a Φ')) := by
    rw [← hGG]
    exact GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ (GlobalTheory.PoissonReindex.mem_schA_reidx e hGGs)
  have hinv := GlobalTheory.SWQ.fourier_inversion F N ψ lam ν a hC Φ' hD1 hD2 hD3
  have hx : T (T.symm x) = x := T.apply_symm_apply x
  have h1 := congrFun hGG (T.symm x)
  rw [hinv, hx] at h1
  have hcomm : ∀ y : κ → AF F, y ⬝ᵥ x = x ⬝ᵥ y := fun y => dotProduct_comm y x
  calc ∫ y, G y * ψ (y ⬝ᵥ x) ∂μ = ∫ z, G z * ψ (z ⬝ᵥ x) ∂μ := rfl
    _ = GlobalTheory.SWQ.Da (-1) Φ' (T.symm x) := h1
    _ = Φ (-x) := by
      simp only [GlobalTheory.SWQ.Da, hΦ', neg_one_smul, map_neg, hx]

end GlobalTheory.TamFourier

end

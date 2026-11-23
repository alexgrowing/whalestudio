import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SchAPairing

theorem eq_of_pairing : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ f ∈ schA F κ, ∀ g ∈ schA F κ,
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ ψ ∈ schA F κ,
      ∫ x, f x * starRingEnd ℂ (ψ x) ∂μ = ∫ x, g x * starRingEnd ℂ (ψ x) ∂μ) → f = g := by
  intro F _ _ κ _ f hf g hg h
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  set μ : Measure (κ → AF F) := Measure.addHaar with hμ
  haveI hH : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  have hd : f - g ∈ schA F κ := Submodule.sub_mem _ hf hg
  have hL : ∀ Φ ∈ schA F κ, MemLp Φ 2 μ := fun Φ hΦ => GlobalTheory.WeilM.schA_memLp_two F κ μ hH Φ hΦ
  have hconj : ∀ Φ ∈ schA F κ, MemLp (fun x => starRingEnd ℂ (Φ x)) 2 μ := fun Φ hΦ => by
    have := hL Φ hΦ
    exact this.star
  have hint : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, Integrable (fun x => Φ x * starRingEnd ℂ (Ψ x)) μ := by
    intro Φ hΦ Ψ hΨ
    have h1 : MemLp Φ 2 μ := hL Φ hΦ
    have h2 : MemLp (fun x => starRingEnd ℂ (Ψ x)) 2 μ := hconj Ψ hΨ
    haveI : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
    exact MemLp.integrable_mul (p := 2) (q := 2) h1 h2
  have h0 : ∫ x, (f - g) x * starRingEnd ℂ ((f - g) x) ∂μ = 0 := by
    have e := h μ hH (f - g) hd
    have e2 : ∫ x, (f - g) x * starRingEnd ℂ ((f - g) x) ∂μ
        = ∫ x, f x * starRingEnd ℂ ((f - g) x) ∂μ - ∫ x, g x * starRingEnd ℂ ((f - g) x) ∂μ := by
      rw [← integral_sub (hint f hf _ hd) (hint g hg _ hd)]
      congr 1
      funext x
      simp only [Pi.sub_apply, sub_mul]
    rw [e2, e, sub_self]
  have hcont : Continuous (f - g) :=
    (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hf).sub (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hg)
  set d := f - g with hdd
  have hre : Integrable (fun x => Complex.normSq (d x)) μ := by
    have := (hint d hd d hd).re
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj]
  have hR : ∫ x, Complex.normSq (d x) ∂μ = 0 := by
    have h3 : ∫ x, d x * starRingEnd ℂ (d x) ∂μ = ((∫ x, Complex.normSq (d x) ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      exact Complex.mul_conj (d x)
    exact_mod_cast h3.symm.trans h0
  have hae : d =ᵐ[μ] 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (d x)) hre).1 hR
    filter_upwards [this] with x hx
    simpa using hx
  have hz : d = 0 := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 hae
  exact sub_eq_zero.1 hz

end GlobalTheory.SchAPairing

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW.KerCusp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_unip {r : ℕ} : Continuous (fun x : BlockIx a r → Ad E => (unip x : GA E a)) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem measurable_integrand {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {X : Type} [MeasurableSpace X] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : Measurable k)
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a)
    (hc : Continuous φ.1) (g : GA E a) :
    Measurable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) := by
  let Φ : invSet E a → (BlockIx a r → Ad E) → ℂ := fun y u => chart φ.1 (unip u * g) y.1
  have hΦ : Measurable (Function.uncurry Φ) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun y => ?_)
    · exact ((φ.2 (unip u * g)).continuousOn).restrict
    · have e : Φ y = fun u => φ.1 (unip u * g * infGL E a y.2.unit) := by
        funext u; exact dif_pos y.2
      rw [e]
      exact (hc.comp ((continuous_unip.mul continuous_const).mul continuous_const)).measurable
  have hy : Measurable (fun x : X => (⟨toL (γ x).val, val_mem_invSet (γ x)⟩ : invSet E a)) :=
    Measurable.subtype_mk hγ
  have e : (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) =
      fun p => k p.2 * Function.uncurry Φ (⟨toL (γ p.2).val, val_mem_invSet (γ p.2)⟩, p.1) := by
    funext p
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, Φ, chart_val]
  rw [e]
  exact (hk.comp measurable_snd).mul (hΦ.comp ((hy.comp measurable_snd).prodMk measurable_fst))

end GlobalTheory.JSW.KerCusp

namespace GlobalTheory.JSW

theorem isCuspidal_kerOp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν _ k γ hk φ hφ r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := hφ.bdd
  have hk0 : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
  have hm := KerCusp.measurable_integrand (r := r) hk.1 hk.2.1 φ hφ.cont g
  have hint : Integrable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) =>
      k x * φ.1 (unip u * g * infGL E a (γ x))) ((μ.restrict 𝓕).prod ν) := by
    refine Integrable.mono' ((integrable_const C).mul_prod hk0) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  change ∫ u in 𝓕, (∫ x, k x * φ.1 (unip u * g * infGL E a (γ x)) ∂ν) ∂μ = 0
  rw [integral_integral_swap hint]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero X ℂ)
  rw [integral_const_mul]
  have e : ∀ u : BlockIx a r → Ad E, unip u * g * infGL E a (γ x) = unip u * (g * infGL E a (γ x)) :=
    fun u => mul_assoc _ _ _
  simp only [e]
  rw [hφ.cusp r h0 h1 μ 𝓕 hμ hF _, mul_zero]

end GlobalTheory.JSW

import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurePreservingPiProd

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

section ProdF

variable {ι : Type} [Fintype ι] {r : ℕ} {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)] [∀ v, MeasurableInv (G v)]

theorem prod_formula (mG : ∀ v, Measure (G v)) [∀ v, SigmaFinite (mG v)]
    (ν : ∀ v, Measure (Fin (r + 1) → ℂ)) [∀ v, SigmaFinite (ν v)]
    (μ μ' : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] [∀ v, SigmaFinite (μ' v)]
    (h : ∀ v, (Fin (r + 1) → ℂ) → G v) (hh : ∀ v, Measurable (h v))
    (hm : ∀ v, mG v = ((ν v).prod ((μ v).prod (μ' v))).map (fun x => x.2.1 * h v x.1 * x.2.2⁻¹))
    (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂Measure.pi mG = ∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => h v (c v)) * s'⁻¹)
      ∂Measure.pi μ' ∂Measure.pi μ ∂Measure.pi ν := by
  have hFm : ∀ v, Measurable
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹) :=
    fun v => ((measurable_fst.comp measurable_snd).mul ((hh v).comp measurable_fst)).mul
      (measurable_snd.comp measurable_snd).inv
  have : ∀ v, SigmaFinite (((ν v).prod ((μ v).prod (μ' v))).map
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹)) := fun v => by
    rw [← hm v]; infer_instance
  have hpi : Measure.pi mG = (Measure.pi fun v => (ν v).prod ((μ v).prod (μ' v))).map
      (fun y v => (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) := by
    rw [Measure.pi_map_pi (fun v => (hFm v).aemeasurable)]
    congr 1; funext v; exact hm v
  have hYm : Measurable (fun (y : (v : ι) → (Fin (r + 1) → ℂ) × (G v × G v)) (v : ι) =>
      (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) :=
    measurable_pi_lambda _ fun v => (hFm v).comp (measurable_pi_apply v)
  have hgm : Measurable (fun z : ((v : ι) → (Fin (r + 1) → ℂ)) × (((v : ι) → G v) × ((v : ι) → G v)) =>
      φ (z.2.1 * (fun v => h v (z.1 v)) * z.2.2⁻¹)) := by
    refine hφ.comp (((measurable_fst.comp measurable_snd).mul ?_).mul
      (measurable_snd.comp measurable_snd).inv)
    exact measurable_pi_lambda _ fun v => (hh v).comp ((measurable_pi_apply v).comp measurable_fst)
  have hE1 := measurePreserving_piProd (α := fun _ => Fin (r + 1) → ℂ) (β := fun v => G v × G v)
    ν (fun v => (μ v).prod (μ' v))
  have hE2 := (MeasurePreserving.id (Measure.pi ν)).prod
    (measurePreserving_piProd (α := G) (β := G) μ μ')
  have hE := hE2.comp hE1
  rw [hpi, lintegral_map hφ hYm]
  refine Eq.trans ?_ ((hE.lintegral_comp hgm).trans ?_)
  · rfl
  rw [lintegral_prod _ hgm.aemeasurable]
  refine lintegral_congr fun c => ?_
  exact lintegral_prod (fun y : ((v : ι) → G v) × ((v : ι) → G v) =>
    φ (y.1 * (fun v => h v (c v)) * y.2⁻¹)) (hgm.comp measurable_prodMk_left).aemeasurable

theorem dc_switch (μ μ' : Measure ((v : ι) → G v)) [SFinite μ'] (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ)
    (γ t t' : (v : ι) → G v) (ht : μ.map (fun x => x * t) = μ) (ht' : μ'.map (fun x => x * t') = μ') :
    ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
  have hΦ : Measurable fun a : (v : ι) → G v => ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' :=
    (hφ.comp ((measurable_fst.mul_const γ).mul measurable_snd.inv)).lintegral_prod_right'
  have inner : ∀ a : (v : ι) → G v,
      ∫⁻ s', φ (a * γ * (s' * t')⁻¹) ∂μ' = ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' := by
    intro a
    have hf : Measurable fun s' : (v : ι) → G v => φ (a * γ * s'⁻¹) :=
      hφ.comp (measurable_const.mul measurable_inv)
    rw [← lintegral_map hf (measurable_mul_const t'), ht']
  calc ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ
      = ∫⁻ s, ∫⁻ s', φ (s * t * γ * (s' * t')⁻¹) ∂μ' ∂μ := by
        refine lintegral_congr fun s => lintegral_congr fun s' => ?_
        congr 1; group
    _ = ∫⁻ s, ∫⁻ s', φ (s * t * γ * s'⁻¹) ∂μ' ∂μ :=
        lintegral_congr fun s => inner (s * t)
    _ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
        rw [← lintegral_map hΦ (measurable_mul_const t), ht]

end ProdF

end Formalism.L2.SG.RealObj.InfCut.ProductExactness

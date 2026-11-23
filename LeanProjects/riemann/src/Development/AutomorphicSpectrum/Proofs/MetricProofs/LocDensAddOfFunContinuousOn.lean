import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem locDens_add_ofFun_continuousOn : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ContinuousOn (locDens A (fun i => P i + LocPot.ofFun (f i) + Θ) j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := by
  intro e X _ A U P f Θ hU hP hΘ hf j
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hm : Continuous (mdisc : (Fin e → Matrix (Fin e) (Fin e) ℂ) → ℂ) := by
    unfold mdisc; fun_prop
  have hf2 : ∀ k, ContDiffOn ℝ 2 (f k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := fun k =>
    (hf k j).of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ContinuousOn (fun y => fun k =>
      (hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (f k ∘ (A.chart j).symm) y +
        hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :
          Matrix (Fin e) (Fin e) ℂ))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    continuousOn_pi.2 fun k =>
      (((hessC_base_continuousOn A (P k) (hP k) j).mono Set.inter_subset_left).add
        (hessC_continuousOn _ _ hVo (hf2 k))).add
        ((hessC_base_continuousOn A Θ hΘ j).mono Set.inter_subset_left)
  have hc := (continuousOn_const (c := (e.factorial : ℝ) * (2 / Real.pi) ^ e)
    (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U)).mul
    (Complex.continuous_re.comp_continuousOn (hm.comp_continuousOn hH))
  refine hc.congr fun y hy => ?_
  unfold locDens maDens
  simp only [Function.comp_apply, Pi.mul_apply]
  congr 3
  funext k
  have hP' := potential_contDiffAt A (P k) (hP k) j hy.1
  have hΘ' := potential_contDiffAt A Θ hΘ j hy.1
  have hf' : ContDiffAt ℝ 2 (f k ∘ (A.chart j).symm) y :=
    (hf2 k).contDiffAt (hVo.mem_nhds hy)
  rw [show (fun y' => (P k + LocPot.ofFun (f k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
    fun y' => ((fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y' +
      (f k ∘ (A.chart j).symm) y') + (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y'
    from rfl]
  rw [hessC_add' _ _ _ (hP'.add hf') hΘ', hessC_add' _ _ _ hP' hf']

end GlobalTheory.CompanionTheory.Ar.Giv

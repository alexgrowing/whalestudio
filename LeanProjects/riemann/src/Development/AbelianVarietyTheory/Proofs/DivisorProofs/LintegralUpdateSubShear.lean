import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory

theorem lintegral_update_sub_shear {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (g : (ι → ℂ) → ℂ) (hg : Measurable g)
    (hgi : ∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v)
    (F : (ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ i) with he
  have he_mp : MeasurePreserving e := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) _

  set c : ({j // j ≠ i} → ℂ) → ℂ := fun x => g (e.symm (x, 0)) with hc
  have hcm : Measurable c :=
    hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  set S : ({j // j ≠ i} → ℂ) × ({j // ¬ j ≠ i} → ℂ) → ({j // j ≠ i} → ℂ) × ({j // ¬ j ≠ i} → ℂ) :=
    fun p => (p.1, p.2 + (fun _ => - c p.1)) with hS
  have hS_mp : MeasurePreserving S (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun x y => y + (fun _ => - c x))
      (MeasurePreserving.id volume) ?_ ?_
    · exact measurable_snd.add (measurable_pi_lambda _ fun _ => (hcm.comp measurable_fst).neg)
    · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _
  have hT : (fun w => Function.update w i (w i - g w)) = e.symm ∘ S ∘ e := by
    funext w
    have hgw : g w = c (e w).1 := by
      apply hgi
      intro j hj
      simp [hc, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hS, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hgw, sub_eq_add_neg]
    · simp [hS, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hk]
  have hmp : MeasurePreserving (e.symm ∘ S ∘ e) :=
    he_mp.symm.comp (hS_mp.comp he_mp)
  have h := hmp.lintegral_comp hF
  rw [← hT] at h
  exact h

end GlobalTheory

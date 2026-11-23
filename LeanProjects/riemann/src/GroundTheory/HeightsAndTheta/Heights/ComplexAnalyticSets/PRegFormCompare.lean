import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace RegularizedFormComparison

open TubeFormComparison

theorem posSemidef_hessC_logReg_comp {n D : ℕ} (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ) (hs : AnalyticAt ℂ s y) :
    (hessC (logReg u ε ∘ s) y).PosSemidef := by
  set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ
  have hτa : AnalyticAt ℂ τ y := by
    refine analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_
    unfold linEval
    exact Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ =>
      analyticAt_const.mul (analyticAt_pi_iff.1 hs j)
  have hsq : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
  have he : logReg u ε ∘ s =
      fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2 := by
    funext z
    have h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      show Real.log (1 + euclPot (τ z)) = _
      congr 2
      simp only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow,
        inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        Real.sq_sqrt hε.le]
      ring
    have h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      field_simp
      ring
    simp only [Function.comp_apply, logReg]
    rw [h1, h2, Real.log_mul hε.ne' (by positivity)]
    ring
  have hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y := by
    intro F c
    have h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F := funext fun z => fderiv_add_const c
    unfold hessC
    rw [h]
  have hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y) :=
    ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)),
    ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y =
      hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y := rfl
  rw [hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]
  have hP : (hessC (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y)).PosSemidef :=
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w
  set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hB]
  rw [← hBJ]
  exact (hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))

theorem maDens_euclPot_nonneg {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hM : (hessC (g ∘ s) y).PosSemidef) :
    0 ≤ maDens (fun k => vecCons g (fun _ : Fin d => euclPot) k ∘ s) y := by
  have hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) := fun _ =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧
      (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef := fun _ => by
    rw [hessC_euclPot]
    refine ⟨?_, ?_⟩
    · simpa using Matrix.PosSemidef.one.add Matrix.PosSemidef.one
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  have key := abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM
  have h0 := (abs_nonneg _).trans key
  rw [one_pow, mul_one] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end RegularizedFormComparison

open TubeFormComparison RegularizedFormComparison in

theorem RegFormCompare.proof : RegFormCompare.Statement := by
  intro n d J A φ f _hJ _hdim hA hφ hfc hfs
  set K := zeroSet J ∩ tsupport f with hKdef
  have hK : IsCompact K := hfs.isCompact.inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d) := by positivity
  refine ⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', -, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hMs := posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa
  have hE := maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs
  by_cases hxf : x ∈ tsupport f
  · have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
      rw [hsx']
      exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
    have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
        (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
      rw [hsx']
      exact hb i x ⟨hxZ, hxf⟩
    have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs
    have hfx : |f x| ≤ max M 0 := (Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)
    have hvx : |v x| ≤ w x := hvw x hxf
    rw [abs_mul, abs_mul]
    calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
        ≤ w x * max M 0 * (3 ^ (d + 1) * c ^ d *
            maDens (fun k => vecCons (logReg u ε) (fun _ => euclPot) k ∘ s) (A *ᵥ x)) := by
          have hwx := hw x
          have hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
          have h1 : |v x| * |f x| ≤ w x * max M 0 := mul_le_mul hvx hfx (abs_nonneg _) (hw x)
          calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
              ≤ w x * max M 0 * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hwx hM0)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC (mul_nonneg (hw x) hE)

end

end GroundTheory.Heights₂.Heights

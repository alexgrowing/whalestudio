import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open PI.UnitaryGroupMassFormula.GsFr PI.UnitaryGroupMassFormula.DLm.Gram
open Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S5

variable {k r : ℕ}

lemma W_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v → herm (Hpk k r) v z = 0 →
      ‖v‖ ^ 2 ≤ C * (herm (Hpk k r) v v).re := by
  have hc1 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => herm (Hpk k r) v z := by
    unfold herm; fun_prop
  have hc2 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) v v).re := by
    unfold herm; fun_prop
  have hWb : IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} := by
    simp only [inWb, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
  set K : Set (Fin (2 * r + k + 1) → ℂ) :=
    Metric.sphere 0 1 ∩ ({v | inWb k r v} ∩ {v | herm (Hpk k r) v z = 0}) with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right (hWb.inter (isClosed_eq hc1 continuous_const))
  have hpos : ∀ v ∈ K, 0 < (herm (Hpk k r) v v).re := by
    rintro v ⟨hv1, hv2, hv3⟩
    refine posV hz hv2 hv3 ?_
    rintro rfl
    simp at hv1
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := fun v => ((herm (Hpk k r) v v).re)⁻¹)
    (hc2.continuousOn.inv₀ fun v hv => (hpos v hv).ne')
  refine ⟨max C 0, le_max_right _ _, fun v hv hvz => ?_⟩
  by_cases h0 : v = 0
  · subst h0; simp [herm]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  set c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ) with hc
  have hwK : c • v ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    · intro i hi; simp [hv i hi]
    · show herm (Hpk k r) (c • v) z = 0
      rw [hm_smul_l, hvz, mul_zero]
  have hf : (herm (Hpk k r) (c • v) (c • v)).re = ‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re := by
    rw [hm_smul_l, hm_smul_r, hc, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hb := hC (c • v) hwK
  have hp := hpos _ hwK
  rw [hf] at hp hb
  have ht : 0 < (herm (Hpk k r) v v).re := by
    have : 0 < ‖v‖⁻¹ ^ 2 := by positivity
    exact pos_of_mul_pos_right hp this.le
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)] at hb
  have hb2 : 1 ≤ C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) := by
    rw [inv_le_iff_one_le_mul₀ hp] at hb; linarith
  have e : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) = (herm (Hpk k r) v v).re := by
    field_simp
  calc ‖v‖ ^ 2 = ‖v‖ ^ 2 * 1 := by ring
    _ ≤ ‖v‖ ^ 2 * (C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = C * (‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) := by ring
    _ = C * (herm (Hpk k r) v v).re := by rw [e]
    _ ≤ max C 0 * (herm (Hpk k r) v v).re := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le

private theorem herm_Hpk_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (c • x) y = c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (c • x)) = c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_Hpk_smul_right_eq_star_mul (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x (c • y) = star c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star (c • y) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x) = star c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [star_smul, smul_dotProduct, smul_eq_mul]

lemma unitH_facts {z v : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hv : v ∈ Wsp k r z) :
    unitH k r v ∈ Wsp k r z ∧ (herm (Hpk k r) (unitH k r v) (unitH k r v)).re ≤ 1 := by
  obtain ⟨hw, ho⟩ := hv
  set s : ℝ := (Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ with hs
  have hU : unitH k r v = (s : ℂ) • v := rfl
  rw [hU]
  refine ⟨⟨fun i hi => by rw [Pi.smul_apply, hw i hi, smul_zero], ?_⟩, ?_⟩
  · show Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) z = 0
    rw [herm_Hpk_smul_left, ho, mul_zero]
  · show (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) ((s : ℂ) • v)).re ≤ 1
    rw [herm_Hpk_smul_left, herm_Hpk_smul_right_eq_star_mul, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    by_cases hpos : 0 < (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re
    · exact le_of_eq (by rw [hs, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne'])
    · rw [hs, Real.sqrt_eq_zero'.2 (not_lt.1 hpos)]
      simp

lemma lift_X' {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hy : y ∈ B.GV k r)
    {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z') (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    Lm k r z z' y *ᵥ u - u ∈ Xsp k r := by
  have e : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) = 0 := by
    have h1 : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) =
        herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y) := by
      unfold xcofL; rw [hm_sum_r]; simp only [star_star]
    rw [h1, ← ginv_cancel hy (xcofL k r z z' y), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_prW_r huW]
    exact huo
  have hlast : gam k r z z' y u (Fin.last r) = 0 := by
    simp only [gam, wv, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [e, mul_zero]
  have hS : Lm k r z z' y *ᵥ u - u = ∑ c, gam k r z z' y u c • fvec k r z' c := by rw [Lm_mulVec]; abel
  rw [hS]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = Fin.last r
  · rw [hc, hlast, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (fv_X z' c hc)

lemma phi_iso' {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {y : B.Mat k r} (hy : y ∈ B.GV k r)
    (hd : (Zhat k r z z' y).det ≠ 0) {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z')
    (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (Phi k r z z' y *ᵥ u) = herm (Hpk k r) u u := by
  rw [Phi_mulVec]
  have hx := sub_prW_X hz (lift_orth hd u)
  have hP := prW_mem hz (y *ᵥ (Lm k r z z' y *ᵥ u))
  have hL := lift_X' hy huW huo
  rw [← herm_add_X hP.1 hP.1 hx hx, aps, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_add_X huW.1 huW.1 hL hL, aps]

lemma Pp_facts {z z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') (g : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' g *ᵥ v ∈ Wsp k r z' ∧ herm (Hpk k r) (PpG z z' g *ᵥ v) (omW' k r z z' g) = 0 ∧
      (herm (Hpk k r) (PpG z z' g *ᵥ v) (PpG z z' g *ᵥ v)).re ≤
        (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v)).re := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  have hPe : PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v -
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g := by
    unfold PpG
    rw [sub_mulVec, ← mulVec_mulVec, Pm_mulVec, Rk_mulVec]
  set p := PI.UnitaryGroupMassFormula.GsFr.prW k r z' v with hp
  set om := omW' k r z z' g with hom
  have hpW : p ∈ Wsp k r z' := prW_mem hz' v
  have homW : om ∈ Wsp k r z' := prW_mem hz' _
  have hνW : nuG' z z' g ∈ Wsp k r z' := Wsp_smul _ homW
  rw [hPe]
  refine ⟨Wsp_sub hpW (Wsp_smul _ hνW), ?_⟩
  by_cases h0 : om = 0
  · have hν0 : nuG' z z' g = 0 := by
      show unitH k r om = 0
      rw [h0]; simp [unitH]
    rw [hν0, h0]
    simp [herm]
  have ht := posV hz' homW.1 homW.2 h0
  have hνν : herm (Hpk k r) (nuG' z z' g) (nuG' z z' g) = 1 := nz_unit ht
  set c := herm (Hpk k r) p (nuG' z z' g) with hcdef
  set u := p - c • nuG' z z' g with hu
  have huν : herm (Hpk k r) u (nuG' z z' g) = 0 := by
    rw [hu, hm_sub_l, hm_smul_l, hνν, mul_one, sub_self]
  have hνu : herm (Hpk k r) (nuG' z z' g) u = 0 := by
    rw [hm_symm _ hH, huν, star_zero]
  refine ⟨(nz_orth ht u).1 huν, ?_⟩
  have hpu : p = u + c • nuG' z z' g := by rw [hu, sub_add_cancel]
  have e : herm (Hpk k r) p p = herm (Hpk k r) u u + c * star c := by
    conv_lhs => rw [hpu]
    rw [hm_add_l, hm_add_r, hm_add_r, hm_smul_l, hm_smul_l, hm_smul_r, hm_smul_r, huν, hνu, hνν]
    ring
  rw [e, Complex.add_re]
  have : 0 ≤ (c * star c).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _
  linarith

lemma embedding_mul_vec_factorization (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    ioG z z' g *ᵥ v = Phi k r z z' g *ᵥ (PpG z z' g *ᵥ v) := by
  show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]

lemma sq_bound {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ^ 2 ≤ C) : x ≤ C + 1 := by
  nlinarith [sq_nonneg (x - 1)]

end S5

open S5 in
theorem geometry_boundedness_at_zero : GeomBd0 := by
  intro k r z z' hk hz hz'
  obtain ⟨C1, hC1, hW⟩ := W_bound hz
  obtain ⟨C2, hC2, hW'⟩ := W_bound hz'
  set M := ∑ j : Fin (2 * r + k + 1),
    |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|
    with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hν : ∀ g, ‖nuG z z' g‖ ≤ C1 + 1 := by
    intro g
    have hu := unitH_facts hz (prW_mem hz (xcof k r z z' g))
    have h1 := hW _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC1 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC1
    simpa [nuG, omW] using this
  have hν' : ∀ g, ‖nuG' z z' g‖ ≤ C2 + 1 := by
    intro g
    have hu := unitH_facts hz' (prW_mem hz' (g⁻¹ *ᵥ xcofL k r z z' g))
    have h1 := hW' _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC2 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC2
    simpa [nuG', omW'] using this
  refine ⟨(C1 + 1) + (C2 + 1) + (C1 * M + 1), fun g hg => ⟨?_, ?_, ?_⟩⟩
  · have := hν g; have := mul_nonneg hC1 hM0; linarith
  · have := hν' g; have := mul_nonneg hC1 hM0; linarith
  · have hCM := mul_nonneg hC1 hM0
    have hC : 0 ≤ (C1 + 1) + (C2 + 1) + (C1 * M + 1) := by linarith
    rw [Matrix.norm_le_iff hC]
    intro i j
    have hd := det_ne_of_G hz hz' hg.2
    obtain ⟨huW, huo, hle⟩ := Pp_facts (z := z) hz' g (Pi.single j 1)
    have hiso := phi_iso' hz hg.1 hd huW huo
    set q := Phi k r z z' g *ᵥ (PpG z z' g *ᵥ Pi.single j 1) with hq
    have hqW : q ∈ Wsp k r z := by rw [hq, Phi_mulVec]; exact prW_mem hz _
    have h1 := hW q hqW.1 hqW.2
    rw [hiso] at h1
    have hpM : (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
        (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re ≤ M :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin (2 * r + k + 1) =>
        |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
          (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h2 : ‖q‖ ^ 2 ≤ C1 * M := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpM) hC1)
    have h3 := sq_bound (norm_nonneg q) hCM h2
    have e : ioG z z' g i j = q i := by
      rw [hq, ← embedding_mul_vec_factorization]
      simp
    rw [e]
    have := norm_le_pi_norm q i
    have := hν g
    have := hν' g
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

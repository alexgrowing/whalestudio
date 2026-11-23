import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFderivParametricUniformBoundStatement

open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpLimit

theorem iteratedFDeriv_frac_mul_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W K : Set E} {w : E → ℝ} {g : E → ℂ}
    (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W) (hw : ContDiffOn ℝ ∞ w W)
    (hw0 : ∀ x ∈ W, 0 ≤ w x) (hg : ContDiffOn ℝ ∞ g W) (k : ℕ) :
    ∃ M : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (fun y => ((ε * w y / (1 + ε * w y) : ℝ) : ℂ) * g y) x‖ ≤ ε * M := by
  set S : Set (ℝ × E) := Prod.snd ⁻¹' W ∩ (fun p : ℝ × E => 1 + p.1 * w p.2) ⁻¹' Ioi 0 with hSdef
  have hcont : ContinuousOn (fun p : ℝ × E => 1 + p.1 * w p.2) (Prod.snd ⁻¹' W) :=
    continuousOn_const.add (continuousOn_fst.mul (hw.continuousOn.comp continuousOn_snd fun p hp => hp))
  have hS : IsOpen S := hcont.isOpen_inter_preimage (hW.preimage continuous_snd) isOpen_Ioi
  let Φ : ℝ × E → ℂ := fun p => (w p.2 / (1 + p.1 * w p.2)) • g p.2
  have hΦ : ContDiffOn ℝ ∞ Φ S := by
    have hw' : ContDiffOn ℝ ∞ (fun p : ℝ × E => w p.2) S :=
      hw.comp contDiffOn_snd (fun p hp => hp.1)
    have hg' : ContDiffOn ℝ ∞ (fun p : ℝ × E => g p.2) S :=
      hg.comp contDiffOn_snd (fun p hp => hp.1)
    refine (hw'.div (contDiffOn_const.add (contDiffOn_fst.mul hw')) ?_).smul hg'
    intro p hp
    exact ne_of_gt hp.2
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ S := by
    rintro ⟨ε, x⟩ ⟨hε, hx⟩
    refine ⟨hKW hx, ?_⟩
    show 0 < 1 + ε * w x
    have := mul_nonneg hε.1 (hw0 x (hKW hx))
    linarith
  obtain ⟨M, hM⟩ := GlobalTheory.T.iterated_fderiv_parametric_uniform_bound hS hΦ isCompact_Icc hK hsub k
  refine ⟨M, fun ε hε x hx => ?_⟩
  have hfun : (fun y => ((ε * w y / (1 + ε * w y) : ℝ) : ℂ) * g y) = ε • fun y => Φ (ε, y) := by
    funext y
    simp only [Φ, Pi.smul_apply, smul_smul, Complex.real_smul, mul_div_assoc]
    push_cast
    ring
  have hat : ContDiffAt ℝ k (fun y => Φ (ε, y)) x :=
    ((hΦ.contDiffAt (hS.mem_nhds (hsub ⟨hε, hx⟩))).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by exact_mod_cast le_top)
  rw [hfun, iteratedFDeriv_const_smul_apply hat, norm_smul, Real.norm_of_nonneg hε.1]
  exact mul_le_mul_of_nonneg_left (hM ε hε x hx) hε.1

theorem nonneg_of_powComparable {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r : (ι → ℂ) → ℝ} {C : ℝ}
    (h₀ : IsPosFrame U H₀) (hr : ∀ z ∈ U, Real.exp 1 ≤ r z) (hc : PowComparable U r C H₀ H)
    {z : ι → ℂ} (hz : z ∈ U) (a : n) : 0 ≤ C := by
  have h1 : 1 < r z := lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) (hr z hz)
  have hq : 0 < (form (H₀ z) (Pi.single a 1) (Pi.single a 1)).re := by
    have hpos := (h₀.posDef z hz).diag_pos (i := a)
    have e : form (H₀ z) (Pi.single a 1) (Pi.single a 1) = H₀ z a a := by
      simp [form, dotProduct, mulVec, Pi.single_apply]
    rw [e]
    exact (Complex.pos_iff.1 hpos).1
  obtain ⟨h1', h2'⟩ := hc z hz (Pi.single a 1)
  have h3 : r z ^ (-C) ≤ r z ^ C := le_of_mul_le_mul_right (h1'.trans h2') hq
  have := (Real.rpow_le_rpow_left_iff h1).1 h3
  linarith

theorem tendstoUniformlyOn_iteratedFDeriv_interp {ι n : Type} [Fintype ι] [Fintype n]
    [DecidableEq n] {Cμ κ : ℝ} {χ : ℝ → ℝ} (hχ : IsCutoff χ) (hκ : 2 * Cμ + 2 < κ)
    {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r : (ι → ℂ) → ℝ}
    (h₀ : IsPosFrame U H₀) (h₁ : IsPosFrame U H) (hr : ContDiffOn ℝ ∞ r U)
    (hre : ∀ z ∈ U, Real.exp 1 ≤ r z) (hc : PowComparable U r Cμ H₀ H)
    (K : Set (ι → ℂ)) (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) (a b : n) :
    TendstoUniformlyOn
      (fun (R : ℝ) z => iteratedFDeriv ℝ k (fun x => interp H₀ H (cutWeight χ κ R r) x a b) z)
      (iteratedFDeriv ℝ k fun x => H x a b) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact tendstoUniformlyOn_empty
  have hC : 0 ≤ Cμ := nonneg_of_powComparable h₀ hre hc (hKU hz₀) a
  have hκ0 : 0 < κ := by linarith
  have hr1 : ∀ x ∈ U, 1 ≤ r x := fun x hx =>
    le_trans (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) (hre x hx)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open h₀.isOpen hKU
  obtain ⟨B, hB⟩ := hK.cthickening.exists_bound_of_continuousOn (hr.continuousOn.mono hδU)
  set W := Metric.thickening δ K with hWdef
  have hWo : IsOpen W := Metric.isOpen_thickening
  have hKW : K ⊆ W := Metric.self_subset_thickening hδ K
  have hWU : W ⊆ U := (Metric.thickening_subset_cthickening δ K).trans hδU
  have hrB : ∀ x ∈ W, r x ≤ B := fun x hx =>
    (le_abs_self _).trans (by simpa using hB x (Metric.thickening_subset_cthickening δ K hx))
  set w : (ι → ℂ) → ℝ := fun x => r x ^ κ with hwdef
  set g : (ι → ℂ) → ℂ := fun x => H₀ x a b - H x a b with hgdef
  have hw : ContDiffOn ℝ ∞ w W :=
    (hr.mono hWU).rpow_const_of_ne fun x hx => by linarith [hr1 x (hWU hx)]
  have hw0 : ∀ x ∈ W, 0 ≤ w x := fun x hx => Real.rpow_nonneg (by linarith [hr1 x (hWU hx)]) _
  have hg : ContDiffOn ℝ ∞ g W := ((h₀.smooth a b).sub (h₁.smooth a b)).mono hWU
  obtain ⟨M, hM⟩ := iteratedFDeriv_frac_mul_le hWo hK hKW hw hw0 hg k
  have key : ∀ R : ℝ, 2 ≤ R → B ≤ R ^ 2 → ∀ x ∈ W,
      interp H₀ H (cutWeight χ κ R r) x a b =
        H x a b + ((R ^ (-κ) * w x / (1 + R ^ (-κ) * w x) : ℝ) : ℂ) * g x := by
    intro R hR hRB x hx
    have hrx : 1 ≤ r x := hr1 x (hWU hx)
    have hR0 : 0 < R := by linarith
    have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
    have hχ1 : χ (Real.log (r x) / Real.log R) = 1 := by
      apply hχ.eq_one
      constructor
      · exact div_nonneg (Real.log_nonneg hrx) hlogR.le
      · rw [div_le_iff₀ hlogR]
        have h2 : r x ≤ R ^ 2 := (hrB x hx).trans hRB
        calc Real.log (r x) ≤ Real.log (R ^ 2) := Real.log_le_log (by linarith) h2
          _ = 2 * Real.log R := by rw [Real.log_pow]; norm_num
    have hdiv : (r x / R) ^ κ = R ^ (-κ) * w x := by
      rw [Real.div_rpow (by linarith) hR0.le, Real.rpow_neg hR0.le, hwdef]
      ring
    have hu : 0 ≤ R ^ (-κ) * w x := mul_nonneg (Real.rpow_nonneg hR0.le _) (hw0 x hx)
    simp only [interp, cutWeight]
    rw [hχ1, hdiv]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hgdef]
    generalize R ^ (-κ) * w x = u at hu ⊢
    have e1 : (1 : ℝ) - 1 / (1 + u) = u / (1 + u) := by
      field_simp
      ring
    have e2 : (1 : ℝ) / (1 + u) = 1 - u / (1 + u) := by rw [← e1]; ring
    rw [e1, e2]
    push_cast
    ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hε : Tendsto (fun R : ℝ => R ^ (-κ) * M) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hκ0).mul_const M
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (max B 1),
    hε.eventually (gt_mem_nhds hη)] with R hR2 hRB hRM x hx
  have hRB' : B ≤ R ^ 2 := by
    have h1 : 1 ≤ R := le_trans (le_max_right _ _) hRB
    have h2 : B ≤ R := le_trans (le_max_left _ _) hRB
    nlinarith
  have hxW := hKW hx
  have hR0 : 0 < R := by linarith
  have hat : ∀ y ∈ W, ContDiffAt ℝ k (fun y => H y a b) y := fun y hy =>
    ((h₁.smooth a b).contDiffAt (h₁.isOpen.mem_nhds (hWU hy))).of_le (by exact_mod_cast le_top)
  have hφ : ContDiffOn ℝ ∞
      (fun y => ((R ^ (-κ) * w y / (1 + R ^ (-κ) * w y) : ℝ) : ℂ) * g y) W := by
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_const.mul hw).div (contDiffOn_const.add (contDiffOn_const.mul hw))
        fun y hy => ?_)).mul hg
    have := mul_nonneg (Real.rpow_nonneg hR0.le (-κ)) (hw0 y hy)
    linarith
  have heq : (fun y => interp H₀ H (cutWeight χ κ R r) y a b) =ᶠ[𝓝 x]
      (fun y => H y a b) + fun y => ((R ^ (-κ) * w y / (1 + R ^ (-κ) * w y) : ℝ) : ℂ) * g y :=
    Filter.eventually_of_mem (hWo.mem_nhds hxW) fun y hy => key R hR2 hRB' y hy
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply (hat x hxW)
    ((hφ.contDiffAt (hWo.mem_nhds hxW)).of_le (by exact_mod_cast le_top)), dist_self_add_right]
  have hε01 : R ^ (-κ) ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg hR0.le _, Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)⟩
  exact (hM _ hε01 x hx).trans_lt hRM

end GlobalTheory.InterpLimit

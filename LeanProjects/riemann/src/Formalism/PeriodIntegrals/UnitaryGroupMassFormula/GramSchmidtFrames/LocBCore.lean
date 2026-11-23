import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.SMulVec

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section locb

variable {k r : ℕ}

lemma s_qr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ}
    (H : Matrix (Fin m) (Fin m) ℂ) {u : E → Fin m → ℂ} {c : E → ℂ} (hu : Sm u s) (hc : Sm c s)
    (hc0 : ∀ x ∈ s, c x ≠ 0) : Sm (fun x => qr H (u x) (c x)) s := by
  have hci : Sm (fun x => (c x)⁻¹) s := hc.inv hc0
  have hsu : Sm (fun x => star (u x)) s := sv_iff.2 fun l => by simpa using s_star (sv_iff.1 hu l)
  have hw : Sm (fun x => star (u x) ᵥ* H) s := by
    simp_rw [← Matrix.mulVec_transpose]; exact s_mulVec contDiffOn_const hsu
  refine sm_iff.2 fun i j => ?_
  simp only [qr, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact contDiffOn_const.sub (hci.mul ((sv_iff.1 hu i).mul (sv_iff.1 hw j)))

def omS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ xcofL k r z z' g)

lemma inv_uh {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hL : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hH_sq]
  exact Matrix.inv_eq_left_inv hL

lemma omS_eq (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' g = omS k r z z' g := by
  rw [omW', omS, inv_uh hg]

lemma s_omS (z z' : Fin (2 * r + k + 1) → ℂ) {s : Set (B.Mat k r)} : Sm (fun g => omS k r z z' g) s := by
  unfold omS
  have h1 : Sm (fun g : B.Mat k r => Hpk k r * gᴴ * Hpk k r) s :=
    s_mmul (s_mmul contDiffOn_const (s_ct contDiffOn_id)) contDiffOn_const
  exact s_prW z' (s_mulVec h1 (s_xcofL z z' contDiffOn_id))

lemma locB_core {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    (nu' q : Fin (2 * r + k + 1) → ℂ) (S : B.Mat k r) (hq1 : herm (Hpk k r) q q = 1) (hq : q ∈ Wsp k r z')
    (hS : S ∈ UWset k r z') (hSq : S *ᵥ nu' = q) {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r)
    (hG₀ : 0 < Gf k r z z' g₀) (hre : (herm (Hpk k r) q (omS k r z z' g₀)).re ≤ 0) :
    ∃ (O : Set (B.Mat k r)) (bf : B.Mat k r → B.Mat k r),
        IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bf O ∧
        ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          bf g ∈ UWset k r z' ∧ ∃ t : ℝ, 0 < t ∧ omW' k r z z' (g * bf g) = (t : ℂ) • nu' := by
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  let f1 : B.Mat k r → ℝ := fun g => (herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g => (herm (Hpk k r) q (omS k r z z' g)).re
  have sf1 : Sm f1 Set.univ := s_re (s_herm _ (s_omS z z') (s_omS z z'))
  have sf2 : Sm f2 Set.univ := s_re (s_herm _ contDiffOn_const (s_omS z z'))
  have cf1 : Continuous f1 := (contDiffOn_univ.1 sf1).continuous
  have cf2 : Continuous f2 := (contDiffOn_univ.1 sf2).continuous
  let O : Set (B.Mat k r) := {g | 0 < f1 g} ∩ {g | f2 g < Real.sqrt (f1 g)}
  have hc_re : ∀ g ∈ O, 0 < (1 - herm (Hpk k r) q (nz k r (omS k r z z' g))).re := by
    intro g hg
    have hpos : 0 < Real.sqrt (f1 g) := Real.sqrt_pos.2 hg.1
    have e : (1 - herm (Hpk k r) q (nz k r (omS k r z z' g))).re = 1 - (Real.sqrt (f1 g))⁻¹ * f2 g := by
      unfold nz
      rw [hm_smul_r]
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
      rfl
    rw [e]
    have h3 : f2 g / Real.sqrt (f1 g) < 1 := (div_lt_one hpos).2 hg.2
    rw [div_eq_inv_mul] at h3
    linarith
  refine ⟨O, fun g => qr (Hpk k r) (q - nz k r (omS k r z z' g))
      (1 - herm (Hpk k r) q (nz k r (omS k r z z' g))) * S,
    (isOpen_lt continuous_const cf1).inter (isOpen_lt cf2 (Real.continuous_sqrt.comp cf1)), ?_, ?_, ?_⟩
  · have hω : omS k r z z' g₀ ≠ 0 := by rw [← omS_eq z z' hg₀]; exact omW'_ne hz hz' hg₀ hG₀
    have hm := prW_mem hz' ((Hpk k r * g₀ᴴ * Hpk k r) *ᵥ xcofL k r z z' g₀)
    have h1 : 0 < f1 g₀ := posV hz' hm.1 hm.2 hω
    exact ⟨h1, lt_of_le_of_lt hre (Real.sqrt_pos.2 h1)⟩
  · have hs1 : Sm (fun g => Real.sqrt (f1 g)) O := (sf1.mono (Set.subset_univ _)).sqrt fun g hg => (hg.1).ne'
    have hN : Sm (fun g => ((Real.sqrt (f1 g))⁻¹ : ℝ)) O := hs1.inv fun g hg => (Real.sqrt_pos.2 hg.1).ne'
    have hy : Sm (fun g => nz k r (omS k r z z' g)) O := by
      unfold nz; exact s_smul (s_ofReal hN) (s_omS z z')
    exact s_mmul (s_qr _ (contDiffOn_const.sub hy) (contDiffOn_const.sub (s_herm _ contDiffOn_const hy))
      fun g hg h0 => by have := hc_re g hg; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this)
      contDiffOn_const
  · intro g hg hgG _
    beta_reduce
    have h1 : 0 < f1 g := hg.1
    have hωW : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
    set ω := omS k r z z' g with hωdef
    set y := nz k r ω with hydef
    have hy1 : herm (Hpk k r) y y = 1 := nz_unit h1
    have hyW : inWb k r y := nz_inWb hωW.1
    have hyz : herm (Hpk k r) y z' = 0 := by rw [hydef, nz_herm_l, hωW.2, mul_zero]
    have hc0 : 1 - herm (Hpk k r) q y ≠ 0 := by
      intro h0; have := hc_re g hg; rw [← hydef, h0, Complex.zero_re] at this; exact lt_irrefl _ this
    set c := 1 - herm (Hpk k r) q y with hcdef
    have hqu : herm (Hpk k r) q (q - y) = c := by rw [hm_sub_r, hq1]
    have hcu : c + star c = herm (Hpk k r) (q - y) (q - y) := by
      simp only [hm_sub_l, hm_sub_r]
      rw [hq1, hy1, hm_symm _ hH_ct q y, hcdef, star_sub, star_one]
      ring
    have huW : inWb k r (q - y) := fun i hi => by simp [hq.1 i hi, hyW i hi]
    have huz : herm (Hpk k r) (q - y) z' = 0 := by rw [hm_sub_l, hq.2, hyz, sub_zero]
    have hfix : ∀ v, herm (Hpk k r) v (q - y) = 0 → S *ᵥ v = v → (qr (Hpk k r) (q - y) c * S) *ᵥ v = v := by
      intro v h0 hSv
      rw [← mulVec_mulVec, hSv, qr_fix _ _ h0]
    have hbU : qr (Hpk k r) (q - y) c * S ∈ UWset k r z' := by
      refine ⟨uh_mul _ (qr_uh _ hH_ct _ hc0 hcu) hS.1, fun a => ⟨?_, ?_⟩, ?_⟩
      · exact hfix _ (herm_out_wb (bvec_eI_mid a) huW) (hS.2.1 a).1
      · exact hfix _ (herm_out_wb (bvec_esI_mid a) huW) (hS.2.1 a).2
      · exact hfix _ (by rw [hm_symm _ hH_ct (q - y) z', huz, star_zero]) hS.2.2
    refine ⟨hbU, Real.sqrt (f1 g), Real.sqrt_pos.2 h1, ?_⟩
    have hbν : (qr (Hpk k r) (q - y) c * S) *ᵥ nu' = y := by
      rw [← mulVec_mulVec, hSq, qr_mulVec, hqu, div_self hc0, one_smul, sub_sub_cancel]
    have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hbU.1
    have hinv : (qr (Hpk k r) (q - y) c * S)⁻¹ *ᵥ y = nu' := by
      calc (qr (Hpk k r) (q - y) c * S)⁻¹ *ᵥ y
          = (qr (Hpk k r) (q - y) c * S)⁻¹ *ᵥ ((qr (Hpk k r) (q - y) c * S) *ᵥ nu') := by rw [hbν]
        _ = nu' := by rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    have hscale : ω = ((Real.sqrt (f1 g) : ℝ) : ℂ) • y := by
      rw [hydef]; unfold nz
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h1).ne', Complex.ofReal_one,
        one_smul]
    have e1 := omW'_UW hz hz' Wz.one_mem hbU g
    rw [one_mul] at e1
    rw [e1, omS_eq z z' hgG, ← hωdef, hscale, mulVec_smul, hinv]

theorem locB : LocB := by
  intro k r z z' hk hr hz hz' D0 g₀ hg₀ hG₀
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  by_cases h : (herm (Hpk k r) D0.nu' (omS k r z z' g₀)).re ≤ 0
  · exact locB_core hz hz' D0.nu' D0.nu' 1 D0.nu'_unit D0.nu'_mem Wz'.one_mem (one_mulVec _) hg₀ hG₀ h
  · have hS : qr (Hpk k r) D0.nu' (1 / 2) ∈ UWset k r z' := by
      refine ⟨qr_uh _ hH_ct _ (by norm_num) (by rw [D0.nu'_unit, star_div₀, star_one, star_ofNat]; norm_num),
        fun a => ⟨qr_fix _ _ (herm_out_wb (bvec_eI_mid a) D0.nu'_mem.1),
          qr_fix _ _ (herm_out_wb (bvec_esI_mid a) D0.nu'_mem.1)⟩, qr_fix _ _ ?_⟩
      rw [hm_symm _ hH_ct D0.nu' z', D0.nu'_mem.2, star_zero]
    refine locB_core hz hz' D0.nu' ((-1 : ℂ) • D0.nu') (qr (Hpk k r) D0.nu' (1 / 2)) ?_ ?_ hS ?_ hg₀ hG₀ ?_
    · rw [hm_smul_l, hm_smul_r, D0.nu'_unit]; norm_num
    · exact ⟨fun i hi => by simp [D0.nu'_mem.1 i hi], by rw [hm_smul_l, D0.nu'_mem.2, mul_zero]⟩
    · rw [qr_mulVec, D0.nu'_unit]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [hm_smul_l, neg_one_mul, Complex.neg_re]
      linarith [not_le.1 h]

end locb

end PI.UnitaryGroupMassFormula.GsFr

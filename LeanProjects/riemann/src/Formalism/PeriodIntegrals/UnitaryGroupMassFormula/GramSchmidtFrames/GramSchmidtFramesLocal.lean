import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.WbPartOfInWb

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca3

variable {k r : ℕ}

lemma locA_point {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    (D0 : GfBaseD k r z z') {y : B.Mat k r} (hy : y ∈ B.GV k r) (hG : 0 < Gf k r z z' y) {t : ℝ} (ht : 0 < t)
    (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') :
    Hpk k r * (Am k r z z' D0.nu y)ᴴ * Hpk k r ∈ UWset k r z ∧
      Hpk k r * (Am k r z z' D0.nu y)ᴴ * Hpk k r * y ∈ gfSig D0 := by
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have hd := det_ne_of_G hz hz' hG
  have hm : omW k r z z' y ∈ Wsp k r z := prW_mem hz _
  have hpos : 0 < (herm (Hpk k r) (omW k r z z' y) (omW k r z z' y)).re :=
    posV hz hm.1 hm.2 (omW_ne hz hz' hy hG)
  have he1 : herm (Hpk k r) (ev k r z z' y) (ev k r z z' y) = 1 := nz_unit hpos
  have heW : ev k r z z' y ∈ Wsp k r z := ⟨nz_inWb hm.1, by unfold ev; rw [nz_herm_l, hm.2, mul_zero]⟩
  have hΦW : ∀ u, Phi k r z z' y *ᵥ u ∈ Wsp k r z := fun u => by rw [Phi_mulVec]; exact prW_mem hz _
  have hK5 : ∀ u ∈ D0.U0, herm (Hpk k r) (Phi k r z z' y *ᵥ u) (ev k r z z' y) = 0 := fun u hu => by
    unfold ev; exact (nz_orth hpos _).2 (phi_perp hz hz' D0 hy hd hom' hu)
  set A := Am k r z z' D0.nu y with hA
  have hAu : ∀ u ∈ D0.U0, A *ᵥ u = Phi k r z z' y *ᵥ u := fun u hu => by
    have huW := (D0.isotropic_subspace_eq u).1 hu
    simp only [hA, Am_mulVec, prW_of_mem huW.1, huW.2, zero_smul, sub_zero, sub_self, zero_add, add_zero]
  have hAx : ∀ x ∈ Xsp k r, A *ᵥ x = x := fun x hx => Am_fix _ _ _ _ (prW_of_mid (X_mid hx))
  have hAnu : A *ᵥ D0.nu = ev k r z z' y := by
    simp only [hA, Am_mulVec, prW_of_mem D0.nu_mem, D0.nu_unit, one_smul, sub_self, mulVec_zero, zero_add]
  have hAiso : ∀ v w, herm (Hpk k r) (A *ᵥ v) (A *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    have hp := prW_mem hz v
    have hp' := prW_mem hz w
    have hv : herm (Hpk k r) v w = herm (Hpk k r) (v - prW k r z v) (w - prW k r z w) +
        herm (Hpk k r) (prW k r z v) (prW k r z w) := by
      conv_lhs => rw [← spa (prW k r z v) v, ← spa (prW k r z w) w]
      rw [hm_add_l, hm_add_r, hm_add_r, perp_l hp' v, perp_r hp w]
      ring
    set p := prW k r z v with hpdef
    set p' := prW k r z w with hp'def
    set α := herm (Hpk k r) p D0.nu with hα
    set β := herm (Hpk k r) p' D0.nu with hβ
    have hp0 : p - α • D0.nu ∈ D0.U0 :=
      (D0.isotropic_subspace_eq _).2 ⟨Wsp_sub hp (Wsp_smul _ D0.nu_mem), by rw [hm_sub_l, hm_smul_l, D0.nu_unit, mul_one, sub_self]⟩
    have hp0' : p' - β • D0.nu ∈ D0.U0 :=
      (D0.isotropic_subspace_eq _).2 ⟨Wsp_sub hp' (Wsp_smul _ D0.nu_mem), by rw [hm_sub_l, hm_smul_l, D0.nu_unit, mul_one, sub_self]⟩
    have h0 : herm (Hpk k r) (p - α • D0.nu) D0.nu = 0 := ((D0.isotropic_subspace_eq _).1 hp0).2
    have h0' : herm (Hpk k r) D0.nu (p' - β • D0.nu) = 0 := by
      rw [hm_symm _ hH_ct (p' - β • D0.nu) D0.nu, ((D0.isotropic_subspace_eq _).1 hp0').2, star_zero]
    have hpp : herm (Hpk k r) p p' = herm (Hpk k r) (p - α • D0.nu) (p' - β • D0.nu) + α * star β := by
      conv_lhs => rw [← spa (α • D0.nu) p, ← spa (β • D0.nu) p']
      rw [hm_add_l, hm_add_r, hm_add_r, hm_smul_r, hm_smul_l, hm_smul_l, hm_smul_r, h0, h0', D0.nu_unit]
      ring
    have f1 : herm (Hpk k r) (v - p) (Phi k r z z' y *ᵥ (p' - β • D0.nu)) = 0 := perp_l (hΦW _) v
    have f2 : herm (Hpk k r) (v - p) (ev k r z z' y) = 0 := perp_l heW v
    have f3 : herm (Hpk k r) (Phi k r z z' y *ᵥ (p - α • D0.nu)) (w - p') = 0 := perp_r (hΦW _) w
    have f4 := phi_iso hz D0 hy hd hom' hp0 hp0'
    have f5 : herm (Hpk k r) (Phi k r z z' y *ᵥ (p - α • D0.nu)) (ev k r z z' y) = 0 := hK5 _ hp0
    have f6 : herm (Hpk k r) (ev k r z z' y) (w - p') = 0 := perp_r heW w
    have f7 : herm (Hpk k r) (ev k r z z' y) (Phi k r z z' y *ᵥ (p' - β • D0.nu)) = 0 := by
      rw [hm_symm _ hH_ct _ (ev k r z z' y), hK5 _ hp0', star_zero]
    rw [hA, Am_mulVec, Am_mulVec, ← hpdef, ← hp'def, ← hα, ← hβ, hv, hpp]
    simp only [hm_add_l, hm_add_r, hm_smul_l, hm_smul_r, f1, f2, f3, f4, f5, f6, f7, he1]
    ring
  have hAU : A ∈ UWset k r z :=
    ⟨uh_of_herm _ hAiso, fun a => ⟨Am_fix _ _ _ _ (prW_of_mid (bvec_eI_mid a)),
      Am_fix _ _ _ _ (prW_of_mid (bvec_esI_mid a))⟩, Am_fix _ _ _ _ (prW_self hz)⟩
  have hinv : Hpk k r * Aᴴ * Hpk k r = A⁻¹ := (inv_uh hAU.1).symm
  rw [hinv]
  have haU : A⁻¹ ∈ UWset k r z := Wz.inv_mem A hAU
  have hleft : ∀ v, A⁻¹ *ᵥ (A *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hAU.1), one_mulVec]
  refine ⟨haU, uh_mul _ haU.1 hy, ?_, ?_, ?_, ?_⟩
  · have e := zhat_UW haU Wz'.one_mem y
    rw [mul_one] at e
    have : Gf k r z z' (A⁻¹ * y) = Gf k r z z' y := by unfold Gf Dmin; rw [e]
    rw [this]; exact hG
  · have e1 := omW_UW hz haU Wz'.one_mem y
    rw [mul_one] at e1
    have hsc : omW k r z z' y = ((Real.sqrt (herm (Hpk k r) (omW k r z z' y) (omW k r z z' y)).re : ℝ) : ℂ) •
        ev k r z z' y := by
      unfold ev nz
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one, one_smul]
    refine ⟨_, Real.sqrt_pos.2 hpos, ?_⟩
    rw [e1]
    conv_lhs => rw [hsc]
    rw [mulVec_smul, ← hAnu, hleft]
  · have e2 := omW'_UW hz hz' haU Wz'.one_mem y
    rw [mul_one, inv_one, one_mulVec] at e2
    exact ⟨t, ht, by rw [e2, hom']⟩
  · intro u hu
    have hx := sub_prW_X hz (lift_orth hd u)
    refine ⟨_, hx, _, lift_X D0 hy hom' hu, ?_⟩
    rw [aps, ← mulVec_mulVec]
    have e3 : y *ᵥ (Lm k r z z' y *ᵥ u) =
        A *ᵥ (u + (y *ᵥ (Lm k r z z' y *ᵥ u) - prW k r z (y *ᵥ (Lm k r z z' y *ᵥ u)))) := by
      rw [mulVec_add, hAu u hu, hAx _ hx, Phi_mulVec, aps]
    conv_lhs => rw [e3]
    rw [hleft]

theorem locA : LocA := by
  intro k r z z' hk hr hz hz' D0 g₀ hg₀ hG₀ O bf hO hg₀O hbf hbP
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hY : Sm (fun g => g * bf g) O := s_mmul contDiffOn_id hbf
  have hGr : ∀ (g β : B.Mat k r), β ∈ UWset k r z' → Gf k r z z' (g * β) = Gf k r z z' g := by
    intro g β hβ
    have e := zhat_UW Wz.one_mem hβ g
    rw [one_mul] at e
    unfold Gf Dmin; rw [e]
  let fd : B.Mat k r → ℂ := fun g => (Zhat k r z z' (g * bf g)).det
  let fn : B.Mat k r → ℝ := fun g => (herm (Hpk k r) (omW k r z z' (g * bf g)) (omW k r z z' (g * bf g))).re
  have cd : ContinuousOn fd O := (s_det (s_Zhat z z' hY)).continuousOn
  have cn : ContinuousOn fn O := (s_re (s_herm _ (s_omW z z' hY) (s_omW z z' hY))).continuousOn
  have hO1 : IsOpen (O ∩ fd ⁻¹' {0}ᶜ) := cd.isOpen_inter_preimage hO isOpen_compl_singleton
  have hO' : IsOpen ((O ∩ fd ⁻¹' {0}ᶜ) ∩ fn ⁻¹' Set.Ioi 0) :=
    (cn.mono Set.inter_subset_left).isOpen_inter_preimage hO1 isOpen_Ioi
  refine ⟨(O ∩ fd ⁻¹' {0}ᶜ) ∩ fn ⁻¹' Set.Ioi 0,
    fun g => Hpk k r * (Am k r z z' D0.nu (g * bf g))ᴴ * Hpk k r, fun g hg => hg.1.1, hO', ?_, ?_, ?_⟩
  · obtain ⟨hb0, -⟩ := hbP g₀ hg₀O hg₀ hG₀
    have hy0 : g₀ * bf g₀ ∈ B.GV k r := uh_mul _ hg₀ hb0.1
    have hG0 : 0 < Gf k r z z' (g₀ * bf g₀) := by rw [hGr _ _ hb0]; exact hG₀
    have hm : omW k r z z' (g₀ * bf g₀) ∈ Wsp k r z := prW_mem hz _
    exact ⟨⟨hg₀O, det_ne_of_G hz hz' hG0⟩, posV hz hm.1 hm.2 (omW_ne hz hz' hy0 hG0)⟩
  · exact s_mmul (s_mmul contDiffOn_const (s_ct (s_Am z z' D0.nu (hY.mono fun g hg => hg.1.1)
      (fun g hg => hg.1.2) (fun g hg => hg.2)))) contDiffOn_const
  · intro g hg hgG hgP
    beta_reduce
    obtain ⟨hbU, t, ht, hom'⟩ := hbP g hg.1.1 hgG hgP
    have hy : g * bf g ∈ B.GV k r := uh_mul _ hgG hbU.1
    have hG : 0 < Gf k r z z' (g * bf g) := by rw [hGr _ _ hbU]; exact hgP
    obtain ⟨h1, h2⟩ := locA_point hz hz' D0 hy hG ht hom'
    exact ⟨h1, by rw [Matrix.mul_assoc]; exact h2⟩

theorem gram_schmidt_frames_local : GsFrames := gsFrames_of_loc locB locA

end loca3

end PI.UnitaryGroupMassFormula.GsFr

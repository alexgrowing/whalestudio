import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DifferentiableZeroModeLiftOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousPointNormSqQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelD

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem cab_core (hP : Ext.PackingCount) (hGT : Ext.GaussianTailBound) (hA : PropAStatement)
    (hS : GSupStatement) (hI : IsSplit P I) (c : ℕ) (hc : c ≤ DF) (σ : E →+* ℂ)
    (ξ : Vsp X.dim) (hξ1 : ‖ξ‖ = 1) (hξI : ∀ a ∈ I, Hf ξ a = 0)
 :
    ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2 := by
  classical
  have hK := Col.hK_of hI
  set η := Col.wmap (IR I) ξ with hη
  have hη1 : ‖η‖ ≤ 1 := by rw [hη, cab_norm_wmap_xi hK hξI, hξ1]
  have hq2 : (2 : ℝ) ≤ P.q := cab_q_ge P
  have hq2n : 2 ≤ P.q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < P.q := by linarith
  have hR0sq := P.hR0
  have hR0ne : P.R0 ≠ 0 := by intro h; rw [h] at hR0sq; norm_num at hR0sq
  have hR0pos : 0 < |P.R0| := abs_pos.mpr hR0ne
  have hlat := cab_YB_abs hI hP P.q
  have hGle : Col.gB (IR I) ≤ X.gA := cab_gB_le (IR I)
  have hGle' : (Col.gB (IR I) : ℝ) ≤ X.gA := by exact_mod_cast hGle
  have hcD : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have h90 : 90 * ((Fintype.card (Fin (Col.gB (IR I))) : ℝ) + c) ≤ |P.R0| ^ 2 := by
    rw [sq_abs, Fintype.card_fin]; nlinarith [hR0sq.2]
  obtain ⟨β, hβ, hjet, hl2⟩ := hA (Fin (Col.gB (IR I))) (Col.YB hI hP P.q) P.q c |P.R0| P.hq (Col.YB_coc hI hP P.q) hR0pos hlat
    (by rw [sq_abs]; exact hR0sq.1) h90 (cabPoly η c) (cabPoly_deg η c)
  have hJ := cab_J_le η hη1 c P.q P.hq
  rw [Fintype.card_fin] at hJ
  have hl2' : (Col.YB hI hP P.q).l2 P.q β ≤ 6 * (c.factorial * (2 / (P.q * Real.pi)) ^ c * (2 / P.q) ^ Fintype.card (Fin (Col.gB (IR I)))) := by
    rw [Fintype.card_fin]; linarith
  have h90' : 90 * (Fintype.card (Fin (Col.gB (IR I))) : ℝ) ≤ |P.R0| ^ 2 := by
    have : (0 : ℝ) ≤ 90 * c := by positivity
    linarith
  set Bsq : ℝ := 12 * (5.12 : ℝ) ^ (Col.gB (IR I)) * c.factorial * (2 / (P.q * Real.pi)) ^ c with hBsq
  have hsup : ∀ t, (Col.YB hI hP P.q).ptN2 P.q β t ≤ Bsq := by
    intro t
    have := cab_sup hS (Col.YB hI hP P.q) P.q c hq2n |P.R0| hR0pos hlat h90' β hβ hl2' t
    rwa [Fintype.card_fin] at this
  have hBsq0 : 0 ≤ Bsq := by rw [hBsq]; positivity
  set B := Real.sqrt Bsq with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBβ : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2 := by
    intro t; rw [hBdef, Real.sq_sqrt hBsq0]; exact hsup t
  have hT2 : ∀ c' v, ‖Col.Tc X I P.q β c' v‖ ≤ B * Real.exp (P.q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(P.q * Real.pi * ‖Col.uc (IR I) v - Col.uc (IR I) (cabOut c' : Vsp X.dim)‖ ^ 2)) := by
    intro c' v
    have := Col.norm_Tc_le hI hB0 hBβ c' v
    rw [Col.uQ_out] at this
    refine this.trans (le_of_eq ?_)
    rw [show cabOut c' = Quotient.out c' from rfl]; ring_nf
  set s' : (Fin 1 → Vsp X.dim) → ℂ := Col.colS X I P.q β with hs'
  have hs'mem : s' ∈ X.Sec P.q 1 := Col.colS_mem hI hP hGT hB0 hBβ hβ
  have hsPd : Differentiable ℂ (Col.sP X I P.q β) := by
    have h1 : Differentiable ℂ s' := hs'mem.1
    let D : Vsp X.dim →L[ℂ] (Fin 1 → Vsp X.dim) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ _
    have : Col.sP X I P.q β = s' ∘ D := by funext v; rfl
    rw [this]; exact h1.comp D.differentiable
  refine ⟨s', hs'mem, ?_, ?_⟩
  · intro xs hxs
    set F0 := Col.F0 I P.q β with hF0
    set R : Vsp X.dim → ℂ := fun v => Col.sP X I P.q β v - F0 v with hR
    have hF0d : Differentiable ℂ F0 := differentiable_zeroModeLift I P.q β hβ.1
    have hRd : Differentiable ℂ R := hsPd.sub hF0d
    have hsplit : Col.sP X I P.q β = F0 + R := by funext v; simp [hR]
    have hd1 : d1 s' c xs = iteratedFDeriv ℂ c (Col.sP X I P.q β) 0 xs :=
      iteratedFDeriv_single_column (contDiff_of_differentiable_fd hsPd c) xs
    have hmain : iteratedFDeriv ℂ c F0 0 xs = (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ :=
      cab_main hK σ hξI β hβ.1 hjet F0 hF0d (fun v hv => zeroModeLift_on_part hI P.q β σ v hv) xs
        (fun k => (hxs k).1)
    have hadd : iteratedFDeriv ℂ c (Col.sP X I P.q β) 0 xs =
        iteratedFDeriv ℂ c F0 0 xs + iteratedFDeriv ℂ c R 0 xs := by
      rw [hsplit, iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hF0d c).contDiffAt
        (contDiff_of_differentiable_fd hRd c).contDiffAt]
      rfl
    rw [hd1, hadd, hmain, add_sub_cancel_left]
    obtain ⟨g', hg', hs, hle⟩ := cab_sum_nz hP hGT hI
    have hbd := cab_R hI hP hGT hβ B hB0 (Col.summable_Tc hI hP hGT hB0 hBβ) hT2
    have htd := cab_tail_deriv R hRd c xs (fun k => (hxs k).2.le) P.q hq0 B hB0 _ hs hbd
    refine htd.trans ?_
    have hstep : B * ((P.q : ℝ) * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
        ∑' a : cabNZ X I, Real.exp (-(Real.pi / 2 * P.q *
          ‖Col.uc (IR I) (cabOut (a : Col.Qc X I) : Vsp X.dim)‖ ^ 2)) ≤
        B * ((P.q : ℝ) * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
          (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0 (E := E) P.q P.R0))) := by
      gcongr
    refine hstep.trans ?_
    have hnum := cab_numeric c (Col.gB (IR I)) X.gA g' (dstar (E := E) P.m) P.q (t0 (E := E) P.q P.R0) hq2 hGle hg'
      (threshold_ge_log_bound P hc) (threshold_ge_rank_log_two P)
    refine hnum.trans (le_of_eq ?_)
    simp only [Par.eps1]
  · have h4 := Col.l2_colS_le_four_mul hI hP hGT hβ hB0 hBβ
    have hJ1 := cab_J_one P (G := Col.gB (IR I)) hc
    have hl2Y : (Col.YB hI hP P.q).l2 P.q β ≤ 6 := by
      have := hl2'; rw [Fintype.card_fin] at this; nlinarith
    have hK6 := twentyfour_le_constant P
    have hf1 : (1 : ℝ) ≤ (c.factorial : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
      nlinarith
    have hK6p : 0 < P.K6 := by linarith
    rw [inv_mul_le_iff₀ hK6p]
    have : P.K6 ≤ P.K6 * (c.factorial : ℝ) ^ 2 := le_mul_of_one_le_right hK6p.le hf1
    have : X.l2 P.q s' ≤ 4 * (Col.YB hI hP P.q).l2 P.q β := h4
    linarith

end

theorem colAbel_holds (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) :
    ColAbelStatement := by
  intro E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI
  exact cab_core hx.1 hx.2.1 hA hS hI c hc σ ξ hξ1 hξI

end ReciprocityTheory.ChartRestriction.G.I2

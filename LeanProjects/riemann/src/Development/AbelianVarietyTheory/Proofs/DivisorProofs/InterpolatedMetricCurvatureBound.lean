import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureHermitianFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedConnectionDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdbarFormInterpolatedHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedFormConstantFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolatedFormDichotomyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolationPositiveFrameStatement

open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpCurvBound

theorem fin_ineq {x y w : ℂ} {σ a b c₀ c₃ k M : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hx : ‖x‖ ≤ c₀ * M * a) (hy : ‖y‖ ≤ c₃ * M * b)
    (hw : |w.re| ≤ k * M * ((1 - σ) * a + σ * b)) :
    |((((1 - σ : ℝ) : ℂ) * x + (σ : ℂ) * y + w).re)| ≤ (|c₀| + |c₃| + k) * M * ((1 - σ) * a + σ * b) := by
  rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have h1 : |x.re| ≤ |c₀| * M * a := (Complex.abs_re_le_norm x).trans (hx.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hM) ha))
  have h2 : |y.re| ≤ |c₃| * M * b := (Complex.abs_re_le_norm y).trans (hy.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hM) hb))
  have hs' : 0 ≤ 1 - σ := by linarith
  have h3 : |(1 - σ) * x.re + σ * y.re + w.re| ≤ (1 - σ) * |x.re| + σ * |y.re| + |w.re| := by
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hs', abs_of_nonneg hσ0]
  have e1 : (1 - σ) * |x.re| ≤ |c₀| * M * ((1 - σ) * a + σ * b) := by
    have : 0 ≤ |c₀| * M * (σ * b) := by positivity
    have : (1 - σ) * |x.re| ≤ (1 - σ) * (|c₀| * M * a) := mul_le_mul_of_nonneg_left h1 hs'
    nlinarith
  have e2 : σ * |y.re| ≤ |c₃| * M * ((1 - σ) * a + σ * b) := by
    have : 0 ≤ |c₃| * M * ((1 - σ) * a) := by positivity
    have : σ * |y.re| ≤ σ * (|c₃| * M * b) := mul_le_mul_of_nonneg_left h2 hσ0
    nlinarith
  nlinarith

theorem interp_curv_bound : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {Cμ C₀ C₂ C₃ K : ℝ} {U : Set (ι → ℂ)} {H₀ H : (ι → ℂ) → Matrix n n ℂ} {r s : (ι → ℂ) → ℝ} {G : (ι → ℂ) → Matrix ι ι ℂ}, IsPosFrame U H₀ → IsPosFrame U H → (∀ z ∈ U, 1 < r z) → ContDiffOn ℝ ∞ s U → (∀ z ∈ U, (G z).PosSemidef) → PowComparable U r Cμ H₀ H → OneFormBound U H₀ G (fun z ξ => conn H z ξ - conn H₀ z ξ) C₂ → TwoFormBound U H G (curv H) C₃ → TwoFormBound U H₀ G (curv H₀) C₀ → (0 ≤ Cμ → WeightBound K Cμ U r s G) → TwoFormBound U (interp H₀ H s) G (curv (interp H₀ H s)) (2 * (|C₀| + |C₃| + 2 * C₂ ^ 2 + 4 * |K| + 3 * K ^ 2)) := by
  intro ι n _ _ _ Cμ C₀ C₂ C₃ K U H₀ H r s G h₀ h hr hs hG hPC hA hF hF₀ hW
  have hC'0 : 0 ≤ |C₀| + |C₃| + 2 * C₂ ^ 2 + 4 * |K| + 3 * K ^ 2 := by positivity
  rcases isEmpty_or_nonempty n with hn | hn
  · intro z hz
    refine ⟨?_, hG z hz, fun ξ η => ?_⟩
    · exact ⟨by ext i; exact isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩
    · have h1 := gnorm_nonneg (G z) ξ
      have h2 := gnorm_nonneg (G z) η
      refine opNorm_le_of_bound (by positivity) fun v => ?_
      rw [Subsingleton.elim v 0]; simp
  obtain ⟨i⟩ := hn
  have hCμ : ∀ z ∈ U, 0 ≤ Cμ := by
    intro z hz
    have hv : (Pi.single i 1 : n → ℂ) ≠ 0 := by
      intro h0; have := congrFun h0 i; simp at this
    have ha := (posDef_iff.1 (h₀.posDef z hz)).2 _ hv
    have ha' : 0 < (form (H₀ z) (Pi.single i 1) (Pi.single i 1)).re := (Complex.lt_def.1 ha).1
    obtain ⟨h1, h2⟩ := hPC z hz (Pi.single i 1)
    have h3 : r z ^ (-Cμ) ≤ r z ^ Cμ := le_of_mul_le_mul_right (h1.trans h2) ha'
    have := (Real.rpow_le_rpow_left_iff (hr z hz)).1 h3
    linarith
  have hWz := fun z (hz : z ∈ U) => hW (hCμ z hz) z hz
  have hPs : IsPosFrame U (interp H₀ H s) :=
    GlobalTheory.T.interpolation_positive_frame h₀ h hs fun z hz => ⟨(hWz z hz).1, (hWz z hz).2.1⟩
  refine twoFormBound_curv_two_mul hPs hG hC'0 fun z hz ξ v => ?_
  obtain ⟨hs0, hs1, hWξ⟩ := hWz z hz
  have hf₀ := h₀.isHermFrame
  have hf := h.isHermFrame
  have hfs := hPs.isHermFrame
  have hsC : ContDiffAt ℝ 2 s z := (hs.contDiffAt (h₀.isOpen.mem_nhds hz)).of_le (by norm_cast)
  have e₀ := GlobalTheory.T.chern_curvature_hermitian_formula (hf₀.two hz) (hf₀.eventually_herm hz) (hf₀.isUnit z hz) ξ v
  have e₁ := GlobalTheory.T.chern_curvature_hermitian_formula (hf.two hz) (hf.eventually_herm hz) (hf.isUnit z hz) ξ v
  have es := GlobalTheory.T.chern_curvature_hermitian_formula (hfs.two hz) (hfs.eventually_herm hz) (hfs.isUnit z hz) ξ v
  have eX := GlobalTheory.T.interpolated_connection_difference (hf₀.one hz) (hf.one hz) (hsC.differentiableAt two_ne_zero) (hf₀.isUnit z hz)
    (hf.isUnit z hz) (hfs.isUnit z hz) ξ v
  have eD := GlobalTheory.T.ddbar_form_interpolated_hermitian (hf₀.two hz) (hf.two hz) hsC (hf₀.eventually_herm hz) (hf.eventually_herm hz)
    (hf₀.isUnit z hz) (hf.isUnit z hz) ξ v
  have eI := GlobalTheory.T.interpolated_form_constant_formula (s z) (h₀.posDef z hz).isHermitian (h.posDef z hz).isHermitian e₀ e₁ es eD eX
  have hreal : starRingEnd ℂ (form (interp H₀ H s z) (curv (interp H₀ H s) z ξ ξ *ᵥ v) v) =
      form (interp H₀ H s z) (curv (interp H₀ H s) z ξ ξ *ᵥ v) v := by
    rw [conj_form (hPs.posDef z hz).isHermitian,
      form_curv (hfs.two hz) (hfs.eventually_herm hz) (hfs.isUnit z hz)]
  have hnorm := (Complex.abs_re_eq_norm.2 (Complex.conj_eq_iff_im.1 hreal)).symm
  have hρ : 0 < r z ^ (-Cμ) := Real.rpow_pos_of_pos (by linarith [hr z hz]) _
  have hρb : r z ^ (-Cμ) * (form (H z) v v).re ≤ (form (H₀ z) v v).re := by
    have h2 := (hPC z hz v).2
    have h3 : r z ^ (-Cμ) * r z ^ Cμ = 1 := by
      rw [Real.rpow_neg (by linarith [hr z hz]), inv_mul_cancel₀ (Real.rpow_pos_of_pos (by linarith [hr z hz]) _).ne']
    calc r z ^ (-Cμ) * (form (H z) v v).re ≤ r z ^ (-Cμ) * (r z ^ Cμ * (form (H₀ z) v v).re) :=
          mul_le_mul_of_nonneg_left h2 hρ.le
      _ = (form (H₀ z) v v).re := by rw [← mul_assoc, h3, one_mul]
  have hY : gnorm (H₀ z) ((conn H z ξ - conn H₀ z ξ) *ᵥ v) ≤ C₂ * gnorm (G z) ξ * gnorm (H₀ z) v :=
    (gnorm_mulVec_le (h₀.posDef z hz) (h₀.posDef z hz).posSemidef _ v).trans
      (mul_le_mul_of_nonneg_right ((hA z hz).2.2 ξ) (gnorm_nonneg _ _))
  have hB := GlobalTheory.T.interpolated_form_dichotomy (h₀.posDef z hz) (h.posDef z hz) hs0 hs1 hρ (gnorm_nonneg (G z) ξ)
    (im_leviForm_apply_self hsC ξ) (hPC z hz v).1 hρb hY eX (hWξ ξ)
  have hΦ₀ := hF₀.norm_form_le hz ξ v
  have hΦ := hF.norm_form_le hz ξ v
  rw [gnorm_sq (h₀.posDef z hz).posSemidef] at hΦ₀
  rw [gnorm_sq (h.posDef z hz).posSemidef] at hΦ
  have hV : gnorm (interp H₀ H s z) v ^ 2 = (1 - s z) * (form (H₀ z) v v).re + s z * (form (H z) v v).re := by
    rw [gnorm_sq (hPs.posDef z hz).posSemidef]
    show (form (((1 - s z : ℝ) : ℂ) • H₀ z + (s z : ℂ) • H z) v v).re = _
    rw [form_add, form_smul, form_smul, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have ha : 0 ≤ (form (H₀ z) v v).re := by rw [← gnorm_sq (h₀.posDef z hz).posSemidef]; positivity
  have hb : 0 ≤ (form (H z) v v).re := by rw [← gnorm_sq (h.posDef z hz).posSemidef]; positivity
  rw [hnorm, eI, hV]
  refine (fin_ineq hs0 hs1 ha hb (sq_nonneg (gnorm (G z) ξ)) hΦ₀ hΦ hB).trans_eq (by ring)

end GlobalTheory.InterpCurvBound

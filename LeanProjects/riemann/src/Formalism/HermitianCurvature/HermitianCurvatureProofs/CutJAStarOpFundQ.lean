import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.MAx2.Adj

noncomputable section

section fund

variable {r : ℕ} {TT : ℝ}

theorem dR_pos {x : E r} (hx : x ∈ Qset r TT) : 0 < dR x := by
  unfold dR
  exact Finset.prod_pos fun l _ => inv_pos.2 (Complex.normSq_pos.2 (hx.1 l))

theorem dR_nonneg (x : E r) : 0 ≤ dR x := by
  unfold dR
  exact Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)

theorem dR_continuousAt {x : E r} (hx : x ∈ Qset r TT) : ContinuousAt (dR (r := r)) x := by
  unfold dR
  refine tendsto_finsetProd _ fun l _ => ?_
  exact ((Complex.continuous_normSq.comp ((continuous_apply l).comp continuous_fst)).continuousAt).inv₀
    (Complex.normSq_pos.2 (hx.1 l)).ne'

def ofAmb (χ : E r → ℝ) (hχ : ContDiff ℝ sm χ) : SmQ r TT :=
  ⟨fun q => ((χ q.1 : ℝ) : ℂ),
    ((Complex.ofRealCLM.contDiff.comp hχ).contDiffOn).congr fun x hx => by simp [MA.ext, hx]⟩

theorem fund0 (h : SmQ r TT) (hh : ∀ V ∈ Test r TT, ip0 h V = 0) : h = 0 := by
  apply S_ext
  intro q0
  show (h : Qp r TT → ℂ) q0 = 0
  by_contra hne
  have hQ : Qset r TT ∈ nhds q0.1 := (Qset_open r TT).mem_nhds q0.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hQ
  let b : ContDiffBump q0.1 := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport b ⊆ Qset r TT := fun x hx => by
    rw [b.tsupport_eq] at hx
    exact hball (Metric.closedBall_subset_ball (show (2 * ε / 3 : ℝ) < ε by linarith) hx)
  have hbc : ContDiff ℝ sm (fun x => b x) := b.contDiff
  set χQ : SmQ r TT := ofAmb (fun x => b x) hbc with hχQ
  have hextχ : MA.ext (χQ : Qp r TT → ℂ) = fun x => ((b x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ Qset r TT
    · simp [MA.ext, hx, hχQ, ofAmb]
    · have : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (hts h'))
      simp [MA.ext, hx, this]
  have hχT : χQ ∈ Test r TT := by
    refine ⟨?_, ?_⟩
    · rw [hextχ]; exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · rw [hextχ]; exact (tsupport_comp_subset Complex.ofReal_zero _).trans hts
  have hVT : χQ * h ∈ Test r TT := test_mul_right hχT h
  have h0 := hh _ hVT

  set G : E r → ℝ := fun x => dR x * (b x * ‖MA.ext (h : Qp r TT → ℂ) x‖ ^ 2) with hG
  have hint : ip0 h (χQ * h) = ((∫ x, G x : ℝ) : ℂ) := by
    unfold ip0
    rw [integral_base_measure, ← integral_complex_ofReal]
    congr 1
    funext x
    by_cases hx : x ∈ Qset r TT
    · simp only [MA.ext, hx, dif_pos, hG, hχQ, ofAmb]
      simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, Complex.conj_ofReal]
      push_cast
      rw [← Complex.mul_conj']
      ring
    · simp [MA.ext, hx, hG]
  rw [hint] at h0
  have hG0 : (∫ x, G x) = 0 := by exact_mod_cast h0
  have hcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Qset r TT
    · have hh' : ContinuousAt (MA.ext (h : Qp r TT → ℂ)) x :=
        ((h.2 : ContDiffOn ℝ sm (MA.ext (h : Qp r TT → ℂ)) (Qset r TT)).continuousOn.continuousAt
          ((Qset_open r TT).mem_nhds hx))
      exact (dR_continuousAt hx).mul (b.continuous.continuousAt.mul (hh'.norm.pow 2))
    · have hx' : x ∉ tsupport b := fun h' => hx (hts h')
      have hev : G =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with y hy
        simp [hG, show b y = 0 from hy]
      exact (continuousAt_const).congr hev.symm
  have hcs : HasCompactSupport G := by
    apply HasCompactSupport.intro (isCompact_closedBall q0.1 (2 * ε / 3))
    intro x hx
    have : b x = 0 := by
      by_contra hb
      have hxs : x ∈ Function.support b := Function.mem_support.2 hb
      rw [b.support_eq] at hxs
      exact hx (Metric.ball_subset_closedBall hxs)
    simp [hG, this]
  have hnn : 0 ≤ G := fun x => mul_nonneg (dR_nonneg x) (mul_nonneg b.nonneg (sq_nonneg _))
  have hpos0 : G q0.1 ≠ 0 := by
    have hb1 : b q0.1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    have he : MA.ext (h : Qp r TT → ℂ) q0.1 = (h : Qp r TT → ℂ) q0 := by simp [MA.ext, q0.2]
    simp only [hG, hb1, one_mul, he]
    exact (mul_pos (dR_pos q0.2) (pow_pos (norm_pos_iff.2 hne) 2)).ne'
  have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure (E r))) hcs hnn hpos0
  linarith

theorem inner_product_sub_left {f g V : SmQ r TT} (hV : V ∈ Test r TT) : ip0 (f - g) V = ip0 f V - ip0 g V := by
  rw [inner_conj_symm_alt, sub_eq_add_neg, inner_add_right_alt hV, inner_neg_right_alt, map_add, map_neg, ← inner_conj_symm_alt, ← inner_conj_symm_alt,
    ← sub_eq_add_neg]

end fund

open Classical in
theorem fundamental_quadratic_identity : SAFundQ := by
  intro P u w h
  funext π
  have key : ∀ V ∈ MA.Test P.r P.TT, MA.ip0 (u π - w π) V = 0 := by
    intro V hV
    have hU : ∀ π', (fun π'' => if π'' = π then V else 0) π' ∈ MA.Test P.r P.TT := by
      intro π'
      by_cases hπ : π' = π
      · simp [hπ, hV]
      · simp [hπ, test_zero]
    have h1 := h _ hU
    have hs : ∀ x : M.Ty P → MA.SmQ P.r P.TT,
        MA.ipA P x (fun π'' => if π'' = π then V else 0) = MA.ip0 (x π) V := by
      intro x
      unfold MA.ipA
      rw [Finset.sum_eq_single π (fun b _ hb => by simp [hb, inner_zero_right_alt]) (by simp)]
      simp
    rw [hs, hs] at h1
    rw [inner_product_sub_left hV, h1, sub_self]
  exact sub_eq_zero.1 (fund0 _ key)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

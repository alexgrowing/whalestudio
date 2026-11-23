import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexTaylor
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix
open scoped ComplexOrder

noncomputable section

namespace ChartBergmanBound

lemma exists_diag {D : ℕ} {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.PosSemidef) :
    ∃ (N : Matrix (Fin D) (Fin D) ℂ) (lam : Fin D → ℝ), Complex.normSq N.det = 1 ∧
      Function.Injective (fun w : Fin D → ℂ => N *ᵥ w) ∧ (∀ j, 0 ≤ lam j) ∧
      H.det = ∏ j, (lam j : ℂ) ∧
      ∀ w : Fin D → ℂ, ((N *ᵥ w) ⬝ᵥ (H *ᵥ star (N *ᵥ w))).re = ∑ j, lam j * ‖w j‖ ^ 2 := by
  classical
  obtain ⟨V, hVu, e, he0, hdet', hspec⟩ : ∃ V ∈ unitary (Matrix (Fin D) (Fin D) ℂ), ∃ e : Fin D → ℝ,
      (∀ j, 0 ≤ e j) ∧ H.det = ∏ j, (e j : ℂ) ∧
        H = V * Matrix.diagonal (fun j => (e j : ℂ)) * star V :=
    ⟨_, hH.1.eigenvectorUnitary.2, hH.1.eigenvalues, hH.eigenvalues_nonneg,
      by rw [hH.1.det_eq_prod_eigenvalues]; rfl, hH.1.spectral_theorem.trans (by rw [Unitary.conjStarAlgAut_apply]; rfl)⟩
  have h1 : star V * V = 1 := Unitary.star_mul_self_of_mem hVu
  refine ⟨(star V)ᵀ, e, ?_, ?_, he0, hdet', ?_⟩
  · have hd : V.det ∈ unitary ℂ := Matrix.det_of_mem_unitary hVu
    have hd1 : star V.det * V.det = 1 := Unitary.star_mul_self_of_mem hd
    rw [det_transpose, star_eq_conjTranspose, det_conjTranspose, Complex.star_def,
      Complex.normSq_conj]
    have : (Complex.normSq V.det : ℂ) = 1 := by
      rw [← Complex.mul_conj, mul_comm, ← Complex.star_def, hd1]
    exact_mod_cast this
  · intro w w' h
    have key : ∀ u : Fin D → ℂ, Vᵀ *ᵥ ((star V)ᵀ *ᵥ u) = u := fun u => by
      rw [mulVec_mulVec, ← transpose_mul, h1, transpose_one, one_mulVec]
    have h' := congrArg (fun u => Vᵀ *ᵥ u) h
    simpa only [key] using h'
  · intro w
    subst hspec
    have hz : ((star V)ᵀ *ᵥ w) ᵥ* V = w := by
      rw [mulVec_transpose, vecMul_vecMul, h1, vecMul_one]
    have hs : star V *ᵥ star ((star V)ᵀ *ᵥ w) = star w := by
      conv_rhs => rw [← hz, star_vecMul]
      rfl
    have hq : ((star V)ᵀ *ᵥ w) ⬝ᵥ ((V * Matrix.diagonal (fun j => (e j : ℂ)) * star V) *ᵥ
        star ((star V)ᵀ *ᵥ w)) = w ⬝ᵥ (Matrix.diagonal (fun j => (e j : ℂ)) *ᵥ star w) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, hs, dotProduct_mulVec, hz]
    rw [hq]
    simp only [dotProduct, mulVec_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_mul, Complex.ofReal_re]

lemma exists_mulVec_bound {D : ℕ} (N : Matrix (Fin D) (Fin D) ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin D → ℂ, ‖N *ᵥ w‖ ≤ C * ‖w‖ := by
  set L := LinearMap.toContinuousLinearMap (Matrix.toLin' N) with hL
  refine ⟨‖L‖ + 1, by positivity, fun w => ?_⟩
  have h : L w = N *ᵥ w := rfl
  calc ‖N *ᵥ w‖ = ‖L w‖ := by rw [h]
    _ ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
    _ ≤ (‖L‖ + 1) * ‖w‖ := by gcongr; linarith

lemma analyticAt_mulVec {D : ℕ} (N : Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun w : Fin D → ℂ => N *ᵥ w) w :=
  (LinearMap.toContinuousLinearMap (Matrix.toLin' N)).analyticAt w

lemma analyticAt_poly {D : ℕ} (a : Fin D → ℂ) (b : Matrix (Fin D) (Fin D) ℂ) (z : Fin D → ℂ) :
    AnalyticAt ℂ (fun z : Fin D → ℂ => a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)) z := by
  have hc : ∀ i, AnalyticAt ℂ (fun z : Fin D → ℂ => z i) z := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z
  have hm : ∀ i, AnalyticAt ℂ (fun z : Fin D → ℂ => (b *ᵥ z) i) z := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt _).comp
      (analyticAt_mulVec b z)
  simp only [dotProduct]
  exact (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hc i)).add
    (Finset.analyticAt_fun_sum _ fun i _ => (hc i).mul (hm i))

lemma measurePreserving_mulVec {D : ℕ} {N : Matrix (Fin D) (Fin D) ℂ}
    (hN : Complex.normSq N.det = 1) :
    MeasurePreserving (fun w : Fin D → ℂ => N *ᵥ w) volume volume := by
  set f : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ) := (Matrix.toLin' N).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hN]
  have hcoe : (f : (Fin D → ℂ) → (Fin D → ℂ)) = fun w => N *ᵥ w := rfl
  refine ⟨?_, ?_⟩
  · rw [← hcoe]
    exact f.continuous_of_finiteDimensional.measurable
  · rw [← hcoe, Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact one_ne_zero),
      hdet]
    simp

lemma gaussDiscMass_pos {lam R : ℝ} (hl : 0 ≤ lam) (hR : 0 < R) : 0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h
  · positivity
  · have hl' : 0 < lam := lt_of_le_of_ne hl (Ne.symm h)
    have : Real.exp (-lam * R ^ 2) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [sq_pos_of_pos hR])
    exact div_pos (mul_pos Real.pi_pos (by linarith)) hl'

lemma tendsto_inv_gaussDiscMass {lam : ℝ} (hl : 0 ≤ lam) :
    Tendsto (fun R => 1 / gaussDiscMass lam R) atTop (𝓝 (lam / Real.pi)) := by
  rcases hl.eq_or_lt with h | h
  · subst h
    have h0 : ∀ R, gaussDiscMass 0 R = Real.pi * R ^ 2 := fun R => if_pos rfl
    simp only [h0, zero_div, one_div]
    exact ((tendsto_pow_atTop two_ne_zero).const_mul_atTop Real.pi_pos).inv_tendsto_atTop
  · have he : Tendsto (fun R : ℝ => Real.exp (-lam * R ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))
    have h2 : Tendsto (fun R : ℝ => lam / (Real.pi * (1 - Real.exp (-lam * R ^ 2)))) atTop
        (𝓝 (lam / (Real.pi * (1 - 0)))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub he))
        (by simp [Real.pi_ne_zero])
    rw [sub_zero, mul_one] at h2
    refine h2.congr fun R => ?_
    simp only [gaussDiscMass, h.ne', if_false, one_div_div]

lemma det_smul_re {D : ℕ} {H : Matrix (Fin D) (Fin D) ℂ} {lam : Fin D → ℝ}
    (hdet : H.det = ∏ j, (lam j : ℂ)) :
    ((((1 / Real.pi : ℝ) : ℂ) • H).det).re = ∏ j, lam j / Real.pi := by
  have : (((1 / Real.pi : ℝ) : ℂ) • H).det = ((∏ j, lam j / Real.pi : ℝ) : ℂ) := by
    rw [det_smul, hdet, Fintype.card_fin]
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [this, Complex.ofReal_re]

end ChartBergmanBound

open ChartBergmanBound in

theorem ChartBergmanBound.proof (hP : PolydiscSubmean.Statement) (hT : ComplexTaylorTwo.Statement) :
    ChartBergmanBound.Statement := by
  intro D U ψ ρ y₀ hU hy₀ hψ hρ hρ0 hlevi ε hε
  have hψ' : ContDiffAt ℝ 2 ψ y₀ := hψ.contDiffAt (hU.mem_nhds hy₀)
  have hH : (hessC ψ y₀).PosSemidef := ReciprocityTheory.AnForm.M.hessC_posSemidef ψ y₀ hψ' hlevi
  obtain ⟨N, lam, hNdet, hNinj, hlam, hdet, hq⟩ := exists_diag hH
  obtain ⟨a, b, hr⟩ := hT D ψ y₀ hψ'
  rw [det_smul_re hdet]
  set Λ : ℝ := ∏ j, lam j / Real.pi with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.prod_nonneg fun j _ => div_nonneg (hlam j) Real.pi_pos.le
  obtain ⟨C, hC0, hC⟩ := exists_mulVec_bound N
  set ρ₀ := ρ y₀ with hρ₀
  have hΛε : Λ < Λ + ε * ρ₀ := lt_add_of_pos_right _ (mul_pos hε hρ0)
  have hlim : Tendsto (fun R => ∏ j, 1 / gaussDiscMass (lam j) R) atTop (𝓝 Λ) :=
    tendsto_finsetProd _ fun j _ => tendsto_inv_gaussDiscMass (hlam j)
  obtain ⟨R, hRlt, hR1⟩ :=
    ((hlim.eventually_mem (Iio_mem_nhds hΛε)).and (eventually_ge_atTop (1 : ℝ))).exists
  have hR0 : 0 < R := by linarith
  set g : ℝ := ∏ j, 1 / gaussDiscMass (lam j) R with hg
  have hIpos : 0 < ∏ j, gaussDiscMass (lam j) R :=
    Finset.prod_pos fun j _ => gaussDiscMass_pos (hlam j) hR0
  have hgI : g * ∏ j, gaussDiscMass (lam j) R = 1 := by
    rw [hg, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => one_div_mul_cancel (gaussDiscMass_pos (hlam j) hR0).ne'
  set K : ℝ := C ^ 2 * R ^ 2 with hK
  have hcont : ContinuousAt (fun t : ℝ => Real.exp (t * K) / (1 - t) * g) 0 :=
    ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt (by norm_num)).mul continuousAt_const
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Real.exp (t * K) / (1 - t) * g < Λ + ε * ρ₀ :=
    hcont.eventually_mem (Iio_mem_nhds (by simpa using hRlt))
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), (Real.exp (t * K) / (1 - t) * g < Λ + ε * ρ₀ ∧ t < 1) ∧
      0 < t :=
    ((hev.and (Iio_mem_nhds one_pos)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ⟨htlt, ht1⟩, ht0⟩ := hev'.exists
  have h1t : 0 < 1 - t := by linarith
  have hρev : ∀ᶠ y in 𝓝 y₀, (1 - t) * ρ₀ < ρ y :=
    (hρ.continuousAt (hU.mem_nhds hy₀)).eventually_mem (Ioi_mem_nhds (by nlinarith))
  obtain ⟨δ₁, hδ₁, hδr⟩ := Metric.eventually_nhds_iff.1 (hr.def ht0)
  obtain ⟨δ₂, hδ₂, hδρ⟩ := Metric.eventually_nhds_iff.1 hρev
  obtain ⟨δ₃, hδ₃, hδU⟩ := Metric.isOpen_iff.1 hU y₀ hy₀
  set δ := min δ₁ (min δ₂ δ₃) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((C * R / δ) ^ 2)
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn F hF
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnbig : (C * R / δ) ^ 2 < n := hn₀.trans_le (by exact_mod_cast le_of_max_le_left hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set s := R / Real.sqrt n with hs
  have hCs : C * s < δ := by
    have h1 : C * R / δ < Real.sqrt n := Real.lt_sqrt_of_sq_lt hnbig
    rw [div_lt_iff₀ hδ0] at h1
    rw [hs, ← mul_div_assoc, div_lt_iff₀ hsqrt]
    linarith
  have hs2 : (n : ℝ) * s ^ 2 = R ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hnpos.le]
    field_simp
  set B := Metric.closedBall (0 : Fin D → ℂ) s with hB
  have hzB : ∀ w ∈ B, ‖N *ᵥ w‖ < δ ∧ (n : ℝ) * ‖N *ᵥ w‖ ^ 2 ≤ K := by
    intro w hw
    have hw' : ‖w‖ ≤ s := by simpa [hB] using hw
    have h1 : ‖N *ᵥ w‖ ≤ C * s := (hC w).trans (by gcongr)
    refine ⟨h1.trans_lt hCs, ?_⟩
    calc (n : ℝ) * ‖N *ᵥ w‖ ^ 2 ≤ n * (C * s) ^ 2 := by gcongr
      _ = C ^ 2 * (n * s ^ 2) := by ring
      _ = K := by rw [hs2]
  have hΦU : ∀ w ∈ B, y₀ + N *ᵥ w ∈ U := fun w hw => hδU (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hzB w hw).1.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  set G : (Fin D → ℂ) → ℂ := fun w => F (y₀ + N *ᵥ w) *
    Complex.exp (((-(n : ℝ) / 2 : ℝ) : ℂ) * (a ⬝ᵥ (N *ᵥ w) + (N *ᵥ w) ⬝ᵥ (b *ᵥ (N *ᵥ w))))
    with hGdef
  have hG0 : G 0 = F y₀ := by simp [hGdef]
  have hGan : AnalyticOnNhd ℂ G B := by
    intro w hw
    have hlin := analyticAt_mulVec N w
    have haff : AnalyticAt ℂ (fun w : Fin D → ℂ => y₀ + N *ᵥ w) w := analyticAt_const.add hlin
    have hPa : AnalyticAt ℂ
        (fun w : Fin D → ℂ => a ⬝ᵥ (N *ᵥ w) + (N *ᵥ w) ⬝ᵥ (b *ᵥ (N *ᵥ w))) w :=
      (analyticAt_poly a b (N *ᵥ w)).comp hlin
    exact ((hF _ (hΦU w hw)).comp_of_eq haff rfl).mul ((analyticAt_const.mul hPa).cexp)
  have hPn := hP D n lam R G (by omega) hR0 hlam hGan
  rw [hG0] at hPn
  set k : ℝ := (1 - t) * ρ₀ * Real.exp (-(n : ℝ) * ψ y₀) * Real.exp (-(t * K)) with hk
  have hk0 : 0 ≤ k := by positivity

  have hpt : ∀ w ∈ B, ENNReal.ofReal (k * (‖G w‖ ^ 2 *
        Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2))) ≤
      ENNReal.ofReal (‖F (y₀ + N *ᵥ w)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (y₀ + N *ᵥ w)) *
        ρ (y₀ + N *ᵥ w)) := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hzδ, hzK⟩ := hzB w hw
    have hqw := hq w
    have hGw : ‖G w‖ ^ 2 = ‖F (y₀ + N *ᵥ w)‖ ^ 2 *
        Real.exp (-(n : ℝ) * (a ⬝ᵥ (N *ᵥ w) + (N *ᵥ w) ⬝ᵥ (b *ᵥ (N *ᵥ w))).re) := by
      simp only [hGdef]
      rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, mul_pow, sq (Real.exp _),
        ← Real.exp_add]
      congr 2
      ring
    set z := N *ᵥ w with hz
    have hzδ₁ : dist z 0 < δ₁ := by
      rw [dist_zero_right]; exact hzδ.trans_le (min_le_left _ _)
    have hzδ₂ : dist (y₀ + z) y₀ < δ₂ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hzδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hrem := hδr hzδ₁
    have hρy := hδρ hzδ₂
    simp only [norm_pow, Real.norm_eq_abs, abs_norm] at hrem
    set r := ψ (y₀ + z) - ψ y₀ - (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re -
      (z ⬝ᵥ (hessC ψ y₀ *ᵥ star z)).re with hrdef
    have hr1 : r ≤ t * ‖z‖ ^ 2 := (le_abs_self _).trans hrem
    have hexp : Real.exp (-(n : ℝ) * ψ (y₀ + z)) =
        Real.exp (-(n : ℝ) * (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re) * Real.exp (-(n : ℝ) * ψ y₀) *
          Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2) * Real.exp (-(n : ℝ) * r) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← hqw, hrdef]
      congr 1
      ring
    have hnr : -(t * K) ≤ -(n : ℝ) * r := by
      have : (n : ℝ) * r ≤ t * K := by
        calc (n : ℝ) * r ≤ n * (t * ‖z‖ ^ 2) := by gcongr
          _ = t * (n * ‖z‖ ^ 2) := by ring
          _ ≤ t * K := by gcongr
      linarith
    rw [hexp, hGw, hk]
    set X := ‖F (y₀ + z)‖ ^ 2 * Real.exp (-(n : ℝ) * (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re) *
      Real.exp (-(n : ℝ) * ψ y₀) * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2) with hX
    have hX0 : 0 ≤ X := by positivity
    calc (1 - t) * ρ₀ * Real.exp (-(n : ℝ) * ψ y₀) * Real.exp (-(t * K)) *
          (‖F (y₀ + z)‖ ^ 2 * Real.exp (-(n : ℝ) * (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re) *
            Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2))
        = X * (Real.exp (-(t * K)) * ((1 - t) * ρ₀)) := by rw [hX]; ring
      _ ≤ X * (Real.exp (-(n : ℝ) * r) * ρ (y₀ + z)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (Real.exp_le_exp.2 hnr) hρy.le
            (by positivity) (Real.exp_pos _).le) hX0
      _ = ‖F (y₀ + z)‖ ^ 2 * (Real.exp (-(n : ℝ) * (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re) *
            Real.exp (-(n : ℝ) * ψ y₀) * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2) *
            Real.exp (-(n : ℝ) * r)) * ρ (y₀ + z) := by rw [hX]; ring

  have hΦ : MeasurePreserving (fun w : Fin D → ℂ => y₀ + N *ᵥ w) volume volume :=
    (measurePreserving_add_left volume y₀).comp (measurePreserving_mulVec hNdet)
  have hemb : MeasurableEmbedding (fun w : Fin D → ℂ => y₀ + N *ᵥ w) := by
    have hker : LinearMap.ker (Matrix.toLin' N) = ⊥ := LinearMap.ker_eq_bot.2 hNinj
    exact ((Homeomorph.addLeft y₀).isClosedEmbedding.comp
      (LinearMap.isClosedEmbedding_of_injective hker)).measurableEmbedding
  have hint : ENNReal.ofReal (∫ w in B, ‖G w‖ ^ 2 *
        Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)) ≤
      ∫⁻ w in B, ENNReal.ofReal (‖G w‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)) := by
    calc _ ≤ ‖∫ w in B, ‖G w‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ w in B, ‖‖G w‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = _ := lintegral_congr fun w => Real.enorm_eq_ofReal (by positivity)
  have hmain : ENNReal.ofReal (k * (‖F y₀‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ *
        ∏ j, gaussDiscMass (lam j) R)) ≤
      ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y) := by
    calc _ ≤ ENNReal.ofReal (k * ∫ w in B, ‖G w‖ ^ 2 *
            Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPn hk0)
      _ = ENNReal.ofReal k * ENNReal.ofReal (∫ w in B, ‖G w‖ ^ 2 *
            Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)) := ENNReal.ofReal_mul hk0
      _ ≤ ENNReal.ofReal k * ∫⁻ w in B, ENNReal.ofReal (‖G w‖ ^ 2 *
            Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)) := by gcongr
      _ = ∫⁻ w in B, ENNReal.ofReal k * ENNReal.ofReal (‖G w‖ ^ 2 *
            Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ w in B, ENNReal.ofReal (k * (‖G w‖ ^ 2 *
            Real.exp (-(n : ℝ) * ∑ j, lam j * ‖w j‖ ^ 2))) :=
          lintegral_congr fun w => (ENNReal.ofReal_mul hk0).symm
      _ ≤ ∫⁻ w in B, ENNReal.ofReal (‖F (y₀ + N *ᵥ w)‖ ^ 2 *
            Real.exp (-(n : ℝ) * ψ (y₀ + N *ᵥ w)) * ρ (y₀ + N *ᵥ w)) :=
          setLIntegral_mono' Metric.isClosed_closedBall.measurableSet hpt
      _ = ∫⁻ y in (fun w : Fin D → ℂ => y₀ + N *ᵥ w) '' B,
            ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y) :=
          hΦ.setLIntegral_comp_emb hemb
            (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y)) B
      _ ≤ _ := lintegral_mono_set (image_subset_iff.2 hΦU)

  have hkey : 1 ≤ (Λ / ρ₀ + ε) *
      ((1 - t) * ρ₀ * Real.exp (-(t * K)) * ∏ j, gaussDiscMass (lam j) R) := by
    have e1 : Real.exp (t * K) * g < (Λ + ε * ρ₀) * (1 - t) := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ h1t] at htlt
      exact htlt
    have e2 : Real.exp (t * K) < (Λ + ε * ρ₀) * (1 - t) * ∏ j, gaussDiscMass (lam j) R := by
      have := mul_lt_mul_of_pos_right e1 hIpos
      rwa [mul_assoc, hgI, mul_one] at this
    have e3 : (Λ / ρ₀ + ε) * ρ₀ = Λ + ε * ρ₀ := by field_simp
    have e4 : Real.exp (t * K) * Real.exp (-(t * K)) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp (t * K) * Real.exp (-(t * K)) := e4.symm
      _ ≤ ((Λ + ε * ρ₀) * (1 - t) * ∏ j, gaussDiscMass (lam j) R) * Real.exp (-(t * K)) :=
          mul_le_mul_of_nonneg_right e2.le (Real.exp_pos _).le
      _ = (Λ / ρ₀ + ε) * ((1 - t) * ρ₀ * Real.exp (-(t * K)) * ∏ j, gaussDiscMass (lam j) R) := by
          rw [← e3]; ring
  have hKc : 0 ≤ (Λ / ρ₀ + ε) * (n : ℝ) ^ D :=
    mul_nonneg (add_nonneg (div_nonneg hΛ0 hρ0.le) hε.le) (by positivity)
  calc ENNReal.ofReal (‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀))
      ≤ ENNReal.ofReal ((Λ / ρ₀ + ε) * (n : ℝ) ^ D) *
          ENNReal.ofReal (k * (‖F y₀‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R)) := by
        rw [← ENNReal.ofReal_mul hKc]
        apply ENNReal.ofReal_le_ofReal
        have hnD : (n : ℝ) ^ D * ((n : ℝ) ^ D)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        calc ‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀)
            = ‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀) * 1 := (mul_one _).symm
          _ ≤ ‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀) * ((Λ / ρ₀ + ε) *
              ((1 - t) * ρ₀ * Real.exp (-(t * K)) * ∏ j, gaussDiscMass (lam j) R)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = (Λ / ρ₀ + ε) * (n : ℝ) ^ D *
              (k * (‖F y₀‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R)) := by
            rw [hk]
            linear_combination (-(‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀) * ((Λ / ρ₀ + ε) *
              ((1 - t) * ρ₀ * Real.exp (-(t * K)) * ∏ j, gaussDiscMass (lam j) R)))) * hnD
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

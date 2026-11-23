import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousHerm
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.IteratedDerivZeroOfBound
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DifferentiableClassFunctionParam

noncomputable section

open MeasureTheory Matrix Filter Topology Metric

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z PositivityTheory.Rg.Sw.WR.T

theorem sPrime_of' (hB : ClsBound) (hGain : ClsGain) (hIBP : IBP) (hI : Integr) (hCh : Chain) (hE : Ext) :
    SPrimeOf := by
  intro hBr hCD n m s hs hmn t ht β hβ
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨N₁, hN₁⟩ := hCD n m s hs hmn
  have hGN := fun N => hGain n s hs m 0 N 1
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((m + 0 + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, cls s z m 0 1 y * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((m + 0 + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))
  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z m 0 1)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z m 0 1)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hgood : ∀ z : ℂ, (n : ℝ) ^ 2 / 2 < z.re → Good (cls (n := n) s z m 0 1) := by
    intro z hz
    have hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2 := by positivity
    refine ⟨(hB n s hs m 0 1 z).1, fun L => ?_⟩
    obtain ⟨C, hC⟩ := (hB n s hs m 0 1 z).2 L
    exact ⟨fun y => C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, cls s z m 0 1 y * chr t β y
    rw [ibp_iter hIBP (hgood z hz) t β ht hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((m + 0 + N : ℕ) : ℝ) ≤ ((m + 0 + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((m + 0 + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith

  set Ns : ℕ := max (n ^ 2 + 3) N₁ with hNs
  have hdiv : DivZ (n - m) ((cayF (n := n) s m)^[Ns] 1) := hN₁ Ns (le_max_right _ _)
  have hNs3 : ((n ^ 2 + 3 : ℕ) : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast le_max_left _ _
  set κ : ℝ := ((m + 0 + Ns : ℕ) : ℝ) / 2 with hκ
  have hκ1 : (n : ℝ) ^ 2 / 2 + 1 < κ := by
    rw [hκ]; push_cast at hNs3 ⊢
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hball : ball (0 : ℂ) 1 ⊆ U Ns := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    show (n : ℝ) ^ 2 / 2 < z.re + κ
    have := Complex.abs_re_le_norm z
    have := neg_abs_le z.re
    linarith

  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ w ∈ closedBall (0 : ℂ) 1, ‖∑ j, ‖(a Ns j).eval w‖‖ ≤ A :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (continuous_finsetSum _ fun j _ => (Polynomial.continuous _).norm).continuousOn
  set CGp : ℝ := max (CG Ns) 0 with hCGp
  set M : E n → ℝ := fun y => A * CGp * (dP y ^ (1 - κ) + dP y ^ (-1 - κ)) with hM
  have hMint : Integrable M := by
    have h1 := hint (κ - 1) (by linarith)
    have h2 := hint (κ + 1) (by linarith)
    refine ((h1.add h2).const_mul (A * CGp)).congr (ae_of_all _ fun y => ?_)
    simp only [hM, Pi.add_apply]
    congr 2 <;> congr 1 <;> ring
  have hpt : ∀ (y : E n) (z : ℂ), ‖z‖ ≤ 1 → ‖(Delta^[Ns] (cls s z m 0 1)) y‖ ≤ ‖z‖ ^ (n - m) * M y := by
    intro y z hz
    obtain ⟨q, hqd, hq⟩ := factor hE hCh hBr hs m Ns (n - m) hdiv y
    have hp := dP_pos hI y
    have hcircle : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ (n - m) * q w‖ ≤ M y := by
      intro w hw
      rw [← hq w, hGeq Ns w y, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
      have hre : |w.re - 0| ≤ 1 := by rw [sub_zero]; exact (Complex.abs_re_le_norm w).trans hw.le
      have r1 := rpow_neg_le_add (dP y) w.re 0 1 hp hre
      have hs1 : ‖∑ j, (a Ns j).eval w * G Ns j y‖ ≤ A * (CGp * dP y ^ (-κ)) := by
        refine (norm_sum_le _ _).trans ?_
        have hb1 : ∀ j, ‖(a Ns j).eval w * G Ns j y‖ ≤ ‖(a Ns j).eval w‖ * (CGp * dP y ^ (-κ)) := by
          intro j
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((hCG' Ns j y).trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _)
        refine (Finset.sum_le_sum fun j _ => hb1 j).trans ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hp.le _))
        have := hA w (by rw [mem_closedBall_zero_iff]; exact hw.le)
        rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at this
      calc dP y ^ (-w.re) * ‖∑ j, (a Ns j).eval w * G Ns j y‖
          ≤ (dP y ^ (-(0 - 1)) + dP y ^ (-(0 + 1))) * (A * (CGp * dP y ^ (-κ))) :=
            mul_le_mul r1 hs1 (norm_nonneg _) (by positivity)
        _ = M y := by
            rw [hM]
            have e1 : dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (1 - κ) := by
              rw [← Real.rpow_add hp]; congr 1; ring
            have e2 : dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (-1 - κ) := by
              rw [← Real.rpow_add hp]; congr 1; ring
            simp only []
            calc (dP y ^ (-(0 - 1 : ℝ)) + dP y ^ (-(0 + 1 : ℝ))) * (A * (CGp * dP y ^ (-κ)))
                = A * CGp * (dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) + dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ)) := by ring
              _ = _ := by rw [e1, e2]
    have hqz := norm_le_of_circle hqd hcircle hz
    rw [hq z, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hqz (by positivity)
  have hWbound : ∀ z ∈ ball (0 : ℂ) 1, ‖WN Ns z‖ ≤ (‖KK‖ ^ Ns * ∫ y, M y) * ‖z‖ ^ (n - m) := by
    intro z hz
    have hzU := hball hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have e : WN Ns z = KK ^ Ns * ∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y := by
      show KK ^ Ns * _ = _
      rw [hsum Ns z hzU]
    rw [e, norm_mul, norm_pow]
    have hi : ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ∫ y, ‖z‖ ^ (n - m) * M y := by
      refine norm_integral_le_of_norm_le (hMint.const_mul _) (ae_of_all _ fun y => ?_)
      rw [norm_mul, norm_chr, mul_one]
      exact hpt y z hz1
    rw [integral_const_mul] at hi
    calc ‖KK‖ ^ Ns * ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ‖KK‖ ^ Ns * (‖z‖ ^ (n - m) * ∫ y, M y) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · obtain ⟨C, hC⟩ := (hB n s hs m 0 1 z).2 []
    have hC0 : ∀ y : E n, ‖cls s z m 0 1 y‖ ≤ C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)) := by
      intro y
      have := hC y
      simpa using this
    have hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2 := by positivity
    refine Integrable.mono' ((hint (z.re + ((m : ℝ) + (0 : ℕ)) / 2) (by linarith)).const_mul C)
      (((hB n s hs m 0 1 z).1.continuous.mul (continuous_chr t β)).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, norm_chr, mul_one]
    exact hC0 y
  · exact hbig (Nf z) z hz
  · intro j hj
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 0] WN Ns :=
      Filter.eventuallyEq_of_mem ((hUopen Ns).mem_nhds (hball (mem_ball_self one_pos))) fun z hz =>
        agree' _ _ z (hNf z) hz
    rw [hev.iteratedDeriv_eq]
    exact iteratedDeriv_zero_of_bound one_pos ((hWdiff Ns).mono hball) hWbound hj

end PositivityTheory.Rg.Sw.SP

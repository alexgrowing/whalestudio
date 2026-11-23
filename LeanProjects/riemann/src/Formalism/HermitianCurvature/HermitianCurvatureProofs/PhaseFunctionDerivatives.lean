import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourierUniquenessMirabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CuspidalIrreducibleSubrep

section PartA

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

open Formalism.FourierDecayAlt.G

theorem phase_function_eq_sum_add_prod_inv {n : ℕ} (D' : ℂ) :
    g0 (n := n) D' = (fun x => ∑ k, x k) + D' • (fun x : Fin n → ℂ => ∏ k, (x k)⁻¹) := by
  funext x
  simp [g0, div_eq_mul_inv, Finset.prod_inv_distrib]

theorem a_isOpen (n : ℕ) : IsOpen {x : Fin n → ℂ | ∀ k, x k ≠ 0} := by
  have : {x : Fin n → ℂ | ∀ k, x k ≠ 0} = ⋂ k, {x | x k ≠ 0} := by ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply k) continuous_const

theorem a_contDiffAt_inv {n : ℕ} (N : WithTop ℕ∞) (k : Fin n) (x : Fin n → ℂ) (hx : x k ≠ 0) :
    ContDiffAt ℂ N (fun y : Fin n → ℂ => (y k)⁻¹) x :=
  ((contDiff_apply ℂ ℂ k).contDiffAt).inv hx

theorem a_norm_proj_le {n : ℕ} (k : Fin n) :
    ‖(ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_le_pi_norm v k

theorem norm_iteratedFDeriv_inv (c : ℕ) (w : ℂ) (hw : w ≠ 0) :
    ‖iteratedFDeriv ℂ c (Inv.inv : ℂ → ℂ) w‖ = c.factorial * (‖w‖⁻¹ * ‖w‖⁻¹ ^ c) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv,
    zpow_sub₀ hw, _root_.zpow_neg_one, zpow_natCast]
  simp [div_eq_mul_inv]

theorem a_norm_inv {n : ℕ} (c : ℕ) (k : Fin n) (x : Fin n → ℂ) (hx : x k ≠ 0) :
    ‖iteratedFDeriv ℂ c (fun y : Fin n → ℂ => (y k)⁻¹) x‖ ≤ c.factorial * (‖x k‖⁻¹ * ‖x k‖⁻¹ ^ c) := by
  have hs : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  obtain ⟨g, hg⟩ : ∃ g : (Fin n → ℂ) →L[ℂ] ℂ, g = ContinuousLinearMap.proj k := ⟨_, rfl⟩
  have hgx : g x = x k := by rw [hg]; rfl
  have hs' : IsOpen (g ⁻¹' ({0}ᶜ : Set ℂ)) := hs.preimage g.continuous
  have hmem : g x ∈ ({0}ᶜ : Set ℂ) := by rw [hgx]; simpa using hx
  have hcd : ContDiffOn ℂ c (Inv.inv : ℂ → ℂ) {0}ᶜ :=
    fun w hw => (contDiffAt_inv ℂ (by simpa using hw)).contDiffWithinAt
  have h := g.iteratedFDerivWithin_comp_right hcd hs.uniqueDiffOn hs'.uniqueDiffOn (x := x) hmem
    (i := c) le_rfl
  rw [iteratedFDerivWithin_of_isOpen c hs' hmem, iteratedFDerivWithin_of_isOpen c hs hmem] at h
  have h2 : (fun y : Fin n → ℂ => (y k)⁻¹) = Inv.inv ∘ g := by rw [hg]; rfl
  rw [h2, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [hgx, norm_iteratedFDeriv_inv c _ hx]
  have h3 : ∏ _i : Fin c, ‖g‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hg ▸ a_norm_proj_le k)
  exact mul_le_of_le_one_right (by positivity) h3

theorem a_lin_zero {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (x : Fin n → ℂ) :
    iteratedFDeriv ℂ (j + 1) (fun x : Fin n → ℂ => ∑ k, x k) x = 0 := by
  obtain ⟨L, hL⟩ : ∃ L : (Fin n → ℂ) →L[ℂ] ℂ, L = ∑ k, ContinuousLinearMap.proj k := ⟨_, rfl⟩
  have h : (fun x : Fin n → ℂ => ∑ k, x k) = L := by
    funext y; rw [hL]; simp
  rw [h, iteratedFDeriv_succ_eq_comp_right]
  have h2 : (fun y => fderiv ℂ (L : (Fin n → ℂ) → ℂ) y) = fun _ => L := by
    funext y; exact L.fderiv
  rw [h2, Function.comp_apply, iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem a_contDiffAt_prod {n : ℕ} (N : WithTop ℕ∞) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) :
    ContDiffAt ℂ N (fun y : Fin n → ℂ => ∏ k, (y k)⁻¹) x :=
  contDiffAt_prod fun k _ => a_contDiffAt_inv N k x (hx k)

theorem a_contDiff_lin {n : ℕ} (N : WithTop ℕ∞) : ContDiff ℂ N (fun x : Fin n → ℂ => ∑ k, x k) :=
  ContDiff.sum fun k _ => contDiff_apply ℂ ℂ k

theorem contDiffAt_phase_function {n : ℕ} (N : WithTop ℕ∞) (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) :
    ContDiffAt ℂ N (g0 D') x := by
  rw [phase_function_eq_sum_add_prod_inv]
  exact (a_contDiff_lin N).contDiffAt.add ((a_contDiffAt_prod N x hx).const_smul D')

noncomputable def a_cst (n N : ℕ) : ℝ :=
  ∑ p ∈ (univ : Finset (Fin n)).sym N, ((p : Multiset (Fin n)).countPerms : ℝ) *
    ∏ k, ((Multiset.count k (p : Multiset (Fin n))).factorial : ℝ)

theorem a_cst_nonneg (n N : ℕ) : 0 ≤ a_cst n N :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem a_prod_bound {n : ℕ} (N : ℕ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) (b : ℝ)
    (hb : ∀ k, ‖x k‖⁻¹ ≤ b) :
    ‖iteratedFDeriv ℂ N (fun y : Fin n → ℂ => ∏ k, (y k)⁻¹) x‖ ≤
      a_cst n N * ((∏ k, ‖x k‖⁻¹) * b ^ N) := by
  have hS := a_isOpen n
  have hxS : x ∈ {x : Fin n → ℂ | ∀ k, x k ≠ 0} := hx
  rw [← iteratedFDerivWithin_of_isOpen N hS hxS]
  have hcd : ∀ k ∈ (univ : Finset (Fin n)),
      ContDiffOn ℂ N (fun y : Fin n → ℂ => (y k)⁻¹) {x : Fin n → ℂ | ∀ k, x k ≠ 0} :=
    fun k _ y hy => (a_contDiffAt_inv N k y (hy k)).contDiffWithinAt
  refine (norm_iteratedFDerivWithin_prod_le hcd hS.uniqueDiffOn hxS le_rfl).trans ?_
  rw [a_cst, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hcard : ∑ k, Multiset.count k (p : Multiset (Fin n)) = N := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact p.2
  calc ∏ k, ‖iteratedFDerivWithin ℂ (Multiset.count k (p : Multiset (Fin n)))
          (fun y : Fin n → ℂ => (y k)⁻¹) {x : Fin n → ℂ | ∀ k, x k ≠ 0} x‖
      ≤ ∏ k, (((Multiset.count k (p : Multiset (Fin n))).factorial : ℝ) *
          (‖x k‖⁻¹ * b ^ (Multiset.count k (p : Multiset (Fin n))))) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
        rw [iteratedFDerivWithin_of_isOpen _ hS hxS]
        refine (a_norm_inv _ k x (hx k)).trans ?_
        gcongr
        exact hb k
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hcard]

theorem a_fderiv_single {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) (k : Fin n) :
    fderiv ℂ (g0 D') x (Pi.single k 1) = dg0 D' x k := by
  have hd : DifferentiableAt ℂ (g0 D') x := (contDiffAt_phase_function 1 D' x hx).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (g0 D') (fderiv ℂ (g0 D') x) (Function.update x k (x k)) := by
    rw [Function.update_eq_self]; exact hd.hasFDerivAt
  have h2 := h1.comp_hasDerivAt (x k) (hasDerivAt_update x k (x k))
  exact h2.unique ((phase_function_deriv n D' x hx).1 k)

theorem a_fderiv_apply {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) (v : Fin n → ℂ) :
    fderiv ℂ (g0 D') x v = ∑ k, v k * dg0 D' x k := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun j => if k = j then (1 : ℂ) else 0) = Pi.single k 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [this, map_smul, a_fderiv_single D' x hx, smul_eq_mul]

end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

theorem phase_relative_deriv : Formalism.FourierDecayAlt.G.PhaseFunctionRelativeDeriv := by
  intro m
  refine ⟨fun D' x hx => ⟨?_, ?_⟩, fun j hj => ⟨a_cst (m + 1) (j + 1), fun D' x r hr hxr => ?_⟩⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    rw [← a_fderiv_single D' x hx k]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [Pi.norm_single]
    simp
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [a_fderiv_apply D' x hx]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖v k * dg0 D' x k‖ ≤ ∑ _k : Fin (m + 1), ‖v‖ * ‖dg0 D' x‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm v k) (norm_le_pi_norm _ k) (norm_nonneg _) (norm_nonneg _)
      _ = ((m : ℝ) + 1) * ‖dg0 D' x‖ * ‖v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  · have hx : ∀ k, x k ≠ 0 := fun k h => by
      have := hxr k
      rw [h, norm_zero] at this
      linarith
    obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image (univ : Finset (Fin (m + 1))) (fun k => ‖x k‖)
      ⟨0, Finset.mem_univ _⟩
    have hpos : ∀ k, 0 < ‖x k‖ := fun k => norm_pos_iff.2 (hx k)
    have hb : ∀ k, ‖x k‖⁻¹ ≤ ‖x k0‖⁻¹ := fun k =>
      inv_anti₀ (hpos k0) (hk0 k (Finset.mem_univ k))
    have h1 : iteratedFDeriv ℂ (j + 1) (g0 D') x =
        D' • iteratedFDeriv ℂ (j + 1) (fun y : Fin (m + 1) → ℂ => ∏ k, (y k)⁻¹) x := by
      have hsm : ContDiffAt ℂ ((j + 1 : ℕ) : WithTop ℕ∞)
          (D' • fun y : Fin (m + 1) → ℂ => ∏ k, (y k)⁻¹) x := (a_contDiffAt_prod _ x hx).const_smul D'
      rw [phase_function_eq_sum_add_prod_inv, iteratedFDeriv_add_apply (a_contDiff_lin _).contDiffAt hsm, a_lin_zero j hj, zero_add,
        iteratedFDeriv_const_smul_apply (a_contDiffAt_prod _ x hx)]
    rw [h1, norm_smul]
    have h2 := a_prod_bound (j + 1) x hx _ hb
    have h3 : ‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹) ≤ 1 + ‖dg0 D' x‖ := by
      have e : D' / (∏ k, x k) / x k0 = 1 - dg0 D' x k0 := by unfold dg0; ring
      have e2 : ‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹) = ‖D' / (∏ k, x k) / x k0‖ := by
        rw [norm_div, norm_div, norm_prod, Finset.prod_inv_distrib]
        ring
      rw [e2, e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      linarith [norm_le_pi_norm (dg0 D' x) k0]
    have h4 : ‖x k0‖⁻¹ ^ j ≤ (r ^ j)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le (hxr k0) j)
    have hc := a_cst_nonneg (m + 1) (j + 1)
    calc ‖D'‖ * ‖iteratedFDeriv ℂ (j + 1) (fun y : Fin (m + 1) → ℂ => ∏ k, (y k)⁻¹) x‖
        ≤ ‖D'‖ * (a_cst (m + 1) (j + 1) * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹ ^ (j + 1))) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = a_cst (m + 1) (j + 1) * (‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹)) * ‖x k0‖⁻¹ ^ j := by ring
      _ ≤ a_cst (m + 1) (j + 1) * (1 + ‖dg0 D' x‖) * (r ^ j)⁻¹ := by
          have h5 : 0 ≤ ‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹) := by positivity
          have h6 : 0 ≤ ‖x k0‖⁻¹ ^ j := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hc) h4 h6
            (mul_nonneg hc (h5.trans h3))

end Formalism.FourierDecayAlt.P

end PartA

section PartB

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

open Formalism.FourierDecayAlt.G

theorem b_pow_sub_one (ω : ℂ) (hω : ‖ω‖ = 1) (i : ℕ) : ‖ω ^ i - 1‖ ≤ i * ‖ω - 1‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : ω ^ (i + 1) - 1 = ω * (ω ^ i - 1) + (ω - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hω, one_mul]
    push_cast
    linarith

theorem b_root_sep (s : ℕ) (hs : 0 < s) (z z' : ℂ) (hz : z ≠ 0) (h : z' ^ s = z ^ s) (hne : z' ≠ z) :
    ‖z‖ ≤ s * ‖z' - z‖ := by
  obtain ⟨ω, hω⟩ : ∃ ω, ω = z' / z := ⟨_, rfl⟩
  have hz' : z' = ω * z := by rw [hω]; field_simp
  have hzs : z ^ s ≠ 0 := pow_ne_zero _ hz
  have hω1 : ω ^ s = 1 := by rw [hω, div_pow, h, div_self hzs]
  have hωne : ω - 1 ≠ 0 := by
    intro h0
    apply hne
    rw [hz', sub_eq_zero.1 h0, one_mul]
  have hn : ‖ω‖ = 1 := by
    have : ‖ω‖ ^ s = 1 := by rw [← norm_pow, hω1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hs.ne').1 this
  have hsum : ∑ i ∈ range s, ω ^ i = 0 := by
    have := mul_geom_sum ω s
    rw [hω1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left hωne
  have h1 : (s : ℂ) = -∑ i ∈ range s, (ω ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have h2 : (s : ℝ) ≤ ∑ i ∈ range s, (s : ℝ) * ‖ω - 1‖ := by
    calc (s : ℝ) = ‖(s : ℂ)‖ := by simp
      _ = ‖∑ i ∈ range s, (ω ^ i - 1)‖ := by rw [h1, norm_neg]
      _ ≤ ∑ i ∈ range s, ‖ω ^ i - 1‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range s, (s : ℝ) * ‖ω - 1‖ := by
        refine Finset.sum_le_sum fun i hi => (b_pow_sub_one ω hn i).trans ?_
        have : (i : ℝ) ≤ s := by exact_mod_cast (Finset.mem_range.1 hi).le
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h3 : 1 ≤ (s : ℝ) * ‖ω - 1‖ := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have h4 : z' - z = (ω - 1) * z := by rw [hz']; ring
  rw [h4, norm_mul, ← mul_assoc]
  exact le_mul_of_one_le_left (norm_nonneg _) h3

theorem b_differentiableAt {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) :
    DifferentiableAt ℂ (g0 D') x := by
  have hP : (∏ k, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hx k
  unfold g0
  fun_prop (disch := assumption)

theorem b_near (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖)
    (x : Fin (m + 1) → ℂ) (hx : ∀ k, ‖x k - z‖ ≤ 2 * δ) (hx0 : ∀ k, x k ≠ 0) (k : Fin (m + 1)) :
    ‖x k - z‖ ≤ 6 * ‖z‖ * ‖dg0 (z ^ (m + 2)) x‖ := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hD : z ^ (m + 2) ≠ 0 := pow_ne_zero _ hz0
  have hδz : 2 * δ ≤ ‖z‖ / (50 * ((m : ℝ) + 2)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, η₀ = ‖dg0 (z ^ (m + 2)) x‖ := ⟨_, rfl⟩
  rw [← hη₀]
  have hη₀0 : 0 ≤ η₀ := hη₀ ▸ norm_nonneg _
  rcases le_or_gt (1 / (16 * ((m : ℝ) + 2))) η₀ with hbig | hsmall
  · calc ‖x k - z‖ ≤ ‖z‖ / (50 * ((m : ℝ) + 2)) := (hx k).trans hδz
      _ ≤ 6 * ‖z‖ * (1 / (16 * ((m : ℝ) + 2))) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        norm_num
      _ ≤ 6 * ‖z‖ * η₀ := by gcongr
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨d, hd⟩ : ∃ d, d = min (e / (6 * ‖z‖)) (1 / (16 * ((m : ℝ) + 2))) := ⟨_, rfl⟩
    have hd0 : 0 < d := by rw [hd]; exact lt_min (by positivity) (by positivity)
    have hd1 : d ≤ e / (6 * ‖z‖) := hd ▸ min_le_left _ _
    have hd2 : d ≤ 1 / (16 * ((m : ℝ) + 2)) := hd ▸ min_le_right _ _
    have h8 : η₀ + d ≤ 1 / (8 * ((m : ℝ) + 2)) := by
      have : 1 / (8 * ((m : ℝ) + 2)) = 1 / (16 * ((m : ℝ) + 2)) + 1 / (16 * ((m : ℝ) + 2)) := by
        field_simp; norm_num
      linarith
    have h4 : η₀ + d ≤ 1 / (4 * ((m : ℝ) + 2)) := by
      refine h8.trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    obtain ⟨z', hz', hxz'⟩ := G1.gradSmall6 m _ hD x hx0 (η₀ + d) (by linarith) h4
      (fun k => lt_of_le_of_lt (hη₀ ▸ norm_le_pi_norm _ k) (by linarith))
    have hnz' : ‖z'‖ = ‖z‖ := by
      have : ‖z'‖ ^ (m + 2) = ‖z‖ ^ (m + 2) := by rw [← norm_pow, hz', norm_pow]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by omega)).1 this
    have hzz : z' = z := by
      by_contra hne
      have hsep := b_root_sep (m + 2) (by omega) z z' hz0 hz' hne
      have h5 : ‖z' - z‖ ≤ ‖x k - z‖ + ‖x k - z'‖ := by
        have : z' - z = (x k - z) - (x k - z') := by ring
        rw [this]; exact norm_sub_le _ _
      have h6 := hxz' k
      rw [hnz'] at h6
      have h7 : 6 * (η₀ + d) * ‖z‖ ≤ 6 * (1 / (8 * ((m : ℝ) + 2))) * ‖z‖ := by gcongr
      have h9 : ‖z' - z‖ ≤ ‖z‖ / (50 * ((m : ℝ) + 2)) + 6 * (1 / (8 * ((m : ℝ) + 2))) * ‖z‖ := by
        linarith [hx k]
      have h10 : ((m + 2 : ℕ) : ℝ) * (‖z‖ / (50 * ((m : ℝ) + 2)) + 6 * (1 / (8 * ((m : ℝ) + 2))) * ‖z‖)
          = (77 / 100) * ‖z‖ := by
        push_cast
        field_simp
        norm_num
      have h11 : ((m + 2 : ℕ) : ℝ) * ‖z' - z‖ ≤ (77 / 100) * ‖z‖ := by
        rw [← h10]
        exact mul_le_mul_of_nonneg_left h9 (Nat.cast_nonneg _)
      linarith
    have h6 := hxz' k
    rw [hzz] at h6
    have h12 : 6 * d * ‖z‖ ≤ e := by
      have := mul_le_mul_of_nonneg_right hd1 (by positivity : (0 : ℝ) ≤ 6 * ‖z‖)
      rw [div_mul_cancel₀ _ (by positivity)] at this
      linarith
    linarith

end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G

theorem phase_near_critical : Formalism.FourierDecayAlt.G.PhaseFunctionNearCritical := by
  intro m δ Rz hδ
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨(2 * ((m : ℝ) + 1) + 2 ^ (m + 1) + 6) * |Rz| + 1, by positivity, ?_⟩
  intro z hz hzR
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hzR' : ‖z‖ ≤ |Rz| := hzR.trans (le_abs_self _)
  have hδz : 4 * δ ≤ ‖z‖ / 2 := by nlinarith
  have hball : ∀ x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)), ∀ k,
      ‖z‖ / 2 ≤ ‖x k‖ ∧ ‖x k‖ ≤ 2 * ‖z‖ := by
    intro x hx k
    rw [mem_ball_iff_norm] at hx
    have h1 : ‖x k - z‖ ≤ ‖x - fun _ => z‖ := norm_le_pi_norm (x - fun _ => z) k
    have h2 : ‖z‖ - ‖x k - z‖ ≤ ‖x k‖ := by
      have : ‖z‖ ≤ ‖x k‖ + ‖x k - z‖ := by
        have e : z = x k - (x k - z) := by ring
        calc ‖z‖ = ‖x k - (x k - z)‖ := by rw [← e]
          _ ≤ _ := norm_sub_le _ _
      linarith
    have h3 : ‖x k‖ ≤ ‖z‖ + ‖x k - z‖ := by
      have e : x k = z + (x k - z) := by ring
      calc ‖x k‖ = ‖z + (x k - z)‖ := by rw [← e]
        _ ≤ _ := norm_add_le _ _
    constructor <;> linarith
  have hne : ∀ x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)), ∀ k, x k ≠ 0 := by
    intro x hx k
    have := (hball x hx k).1
    exact norm_pos_iff.1 (by linarith)
  refine ⟨fun x hx => ⟨hne x hx, ?_⟩, fun x hx => (PhaseFunctionDerivatives.b_differentiableAt _ x (hne x hx)).differentiableWithinAt,
    ?_⟩
  · unfold g0
    have h1 : ‖∑ k, x k‖ ≤ 2 * ((m : ℝ) + 1) * ‖z‖ := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => (hball x hx k).2).trans ?_
      simp
      linarith
    have h2 : (‖z‖ / 2) ^ (m + 1) ≤ ‖∏ k, x k‖ := by
      rw [norm_prod]
      have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin (m + 1) => ‖z‖ / 2)
        (g := fun k => ‖x k‖) (fun _ _ => by positivity) (fun k _ => (hball x hx k).1)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have h3 : ‖z ^ (m + 2) / ∏ k, x k‖ ≤ 2 ^ (m + 1) * ‖z‖ := by
      rw [norm_div, norm_pow, div_le_iff₀ (lt_of_lt_of_le (by positivity) h2)]
      calc ‖z‖ ^ (m + 2) = 2 ^ (m + 1) * ‖z‖ * (‖z‖ / 2) ^ (m + 1) := by
            rw [div_pow]; field_simp; ring
        _ ≤ _ := by gcongr
    refine (norm_add_le _ _).trans ?_
    have h4 : (2 * ((m : ℝ) + 1) + 2 ^ (m + 1) + 6) * ‖z‖ ≤ (2 * ((m : ℝ) + 1) + 2 ^ (m + 1) + 6) * |Rz| := by
      gcongr
    nlinarith
  · intro x hx
    have hx' : x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)) :=
      Metric.closedBall_subset_ball (by linarith) hx
    rw [mem_closedBall_iff_norm] at hx
    have hxk : ∀ k, ‖x k - z‖ ≤ 2 * δ := fun k => (norm_le_pi_norm (x - fun _ => z) k).trans hx
    have hd0 : 0 ≤ ‖dg0 (z ^ (m + 2)) x‖ := norm_nonneg _
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    refine (PhaseFunctionDerivatives.b_near m δ hδ z hz x hxk (hne x hx') k).trans ?_
    apply mul_le_mul_of_nonneg_right _ hd0
    have : (0 : ℝ) ≤ 2 ^ (m + 1) := by positivity
    have h0 : 0 ≤ |Rz| := abs_nonneg _
    nlinarith

end Formalism.FourierDecayAlt.P

end PartB

section PartC

open MeasureTheory

namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

open Formalism.FourierDecayAlt.G

theorem c_le (a : ℝ) (ha : 0 ≤ a) (E' : ℕ) (d A : ℝ) (hd : 0 ≤ d) (hA : (E' : ℝ) + d + 1 ≤ A) :
    (1 + a) ^ E' * (max 1 a) ^ (-A) ≤ 2 ^ ((E' : ℝ) + d + 1) * (1 + a) ^ (-(d + 1)) := by
  have hM1 : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have hM2 : (1 + a) / 2 ≤ max 1 a := by
    rcases le_total a 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (E' : ℝ) + d + 1 := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  rw [← hp] at hA ⊢
  have s1 : (max 1 a) ^ (-A) ≤ (max 1 a) ^ (-p) := Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have s2 : (max 1 a) ^ (-p) ≤ ((1 + a) / 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hM2 (by linarith)
  have s3 : ((1 + a) / 2) ^ (-p) = 2 ^ p * (1 + a) ^ (-p) := by
    rw [Real.div_rpow h1a.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  have s4 : (1 + a) ^ E' * (1 + a) ^ (-p) = (1 + a) ^ (-(d + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add h1a]; congr 1; rw [hp]; ring
  calc (1 + a) ^ E' * (max 1 a) ^ (-A) ≤ (1 + a) ^ E' * (2 ^ p * (1 + a) ^ (-p)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← s3]; exact s1.trans s2
    _ = 2 ^ p * ((1 + a) ^ E' * (1 + a) ^ (-p)) := by ring
    _ = _ := by rw [s4]

theorem c_scale (a τ : ℝ) (ha : 1 ≤ a) (hτ : 1 ≤ τ) (E' : ℕ) (A : ℝ) :
    (1 + τ * a) ^ E' * (max 1 (τ * a)) ^ (-A) ≤
      τ ^ ((E' : ℝ) - A) * ((1 + a) ^ E' * (max 1 a) ^ (-A)) := by
  have hτ0 : 0 < τ := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : 1 ≤ τ * a := by nlinarith
  rw [max_eq_right h1, max_eq_right ha, Real.mul_rpow hτ0.le ha0.le, Real.rpow_sub hτ0, Real.rpow_natCast,
    Real.rpow_neg hτ0.le]
  have h2 : (1 + τ * a) ^ E' ≤ (τ * (1 + a)) ^ E' := pow_le_pow_left₀ (by positivity) (by nlinarith) _
  rw [mul_pow] at h2
  have h3 : 0 ≤ (τ ^ A)⁻¹ * a ^ (-A) := by positivity
  calc (1 + τ * a) ^ E' * ((τ ^ A)⁻¹ * a ^ (-A))
      ≤ (τ ^ E' * (1 + a) ^ E') * ((τ ^ A)⁻¹ * a ^ (-A)) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem c_general {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure] (κ : NNReal) (E' : ℕ) :
    ∃ C : ℝ, ∀ A : ℝ, (E' : ℝ) + (Module.finrank ℝ E : ℝ) + 1 ≤ A →
      Integrable (fun y : E => (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A)) (κ • ν) ∧
      ∫ y : E, (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) ∂(κ • ν) ≤ C ∧
      ∀ τ : ℝ, 1 ≤ τ →
        ∫ y in {y : E | τ ≤ ‖y‖}, (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) ∂(κ • ν) ≤
          C * τ ^ ((E' : ℝ) + (Module.finrank ℝ E : ℝ) - A) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (Module.finrank ℝ E : ℝ) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := hd ▸ Nat.cast_nonneg _
  obtain ⟨G, hG⟩ : ∃ G : E → ℝ, G = fun y => 2 ^ ((E' : ℝ) + d + 1) * (1 + ‖y‖) ^ (-(d + 1)) := ⟨_, rfl⟩
  have hGi : Integrable G ν := by
    rw [hG]; exact (integrable_one_add_norm (by rw [← hd]; linarith)).const_mul _
  have hG0 : ∀ y, 0 ≤ G y := fun y => by rw [hG]; positivity
  refine ⟨κ * ∫ y, G y ∂ν, fun A hA => ?_⟩
  rw [← hd] at hA ⊢
  obtain ⟨F, hF⟩ : ∃ F : E → ℝ, F = fun y : E => (1 + ‖y‖) ^ E' * (max 1 ‖y‖) ^ (-A) := ⟨_, rfl⟩
  rw [← hF]
  have hF0 : ∀ y : E, 0 ≤ F y := fun y => by rw [hF]; positivity
  have hFG : ∀ y : E, F y ≤ G y := fun y => by
    rw [hF, hG]; exact c_le ‖y‖ (norm_nonneg _) E' d A hd0 hA
  have hFm : Measurable F := by rw [hF]; fun_prop
  have hFi : Integrable F ν :=
    hGi.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (hF0 y)]; exact hFG y)
  refine ⟨hFi.smul_measure_nnreal, ?_, fun τ hτ => ?_⟩
  · rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (integral_mono hFi hGi hFG) κ.coe_nonneg
  · have hτ0 : 0 < τ := by linarith
    have hS : MeasurableSet {y : E | τ ≤ ‖y‖} := measurableSet_le measurable_const measurable_norm
    rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ κ.coe_nonneg
    rw [← integral_indicator hS]
    have key := Measure.integral_comp_smul ν ({y : E | τ ≤ ‖y‖}.indicator F) τ
    rw [abs_of_pos (by positivity), smul_eq_mul] at key
    have key2 : ∫ y, {y : E | τ ≤ ‖y‖}.indicator F y ∂ν =
        τ ^ Module.finrank ℝ E * ∫ w, {y : E | τ ≤ ‖y‖}.indicator F (τ • w) ∂ν := by
      rw [key]; field_simp
    have bd : ∫ w, {y : E | τ ≤ ‖y‖}.indicator F (τ • w) ∂ν ≤ ∫ w, τ ^ ((E' : ℝ) - A) * G w ∂ν := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => Set.indicator_nonneg (fun y _ => hF0 y) _)
        (hGi.const_mul _) (Filter.Eventually.of_forall fun w => ?_)
      have hpos : 0 ≤ τ ^ ((E' : ℝ) - A) := by positivity
      by_cases hw : τ ≤ ‖τ • w‖
      · have hn : ‖τ • w‖ = τ * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hτ0.le]
        have hw1 : 1 ≤ ‖w‖ := by
          rw [hn] at hw
          exact le_of_mul_le_mul_left (by linarith) hτ0
        simp only [Set.indicator_of_mem (show τ • w ∈ {y : E | τ ≤ ‖y‖} from hw)]
        have h1 : F (τ • w) ≤ τ ^ ((E' : ℝ) - A) * F w := by
          rw [hF]; simp only [hn]; exact c_scale ‖w‖ τ hw1 hτ E' A
        exact h1.trans (mul_le_mul_of_nonneg_left (hFG w) hpos)
      · simp only [Set.indicator_of_notMem (show τ • w ∉ {y : E | τ ≤ ‖y‖} from hw)]
        exact mul_nonneg hpos (hG0 w)
    rw [integral_const_mul] at bd
    rw [key2]
    calc τ ^ Module.finrank ℝ E * ∫ w, {y : E | τ ≤ ‖y‖}.indicator F (τ • w) ∂ν
        ≤ τ ^ Module.finrank ℝ E * (τ ^ ((E' : ℝ) - A) * ∫ w, G w ∂ν) :=
          mul_le_mul_of_nonneg_left bd (by positivity)
      _ = (∫ w, G w ∂ν) * τ ^ ((E' : ℝ) + d - A) := by
          rw [← Real.rpow_natCast, ← hd, ← mul_assoc, ← Real.rpow_add hτ0, mul_comm]
          congr 2; ring

end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G

theorem majorant_y : Formalism.FourierDecayAlt.G.MajorantY := by
  intro m E' β
  have hfr : (Module.finrank ℝ (UT (m + 2) → ℂ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    rw [G7.finrank_pi, (dimension_count (m + 2)).1]
    push_cast [Nat.add_sub_cancel]
    simp
  have h := PhaseFunctionDerivatives.c_general (volume : Measure (UT (m + 2) → ℂ))
    ((Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (UT (m + 2))) E'
  rw [hfr, ← G7.muPi_eq] at h
  exact h

end Formalism.FourierDecayAlt.P

end PartC

section PartD

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

open Formalism.FourierDecayAlt.G

theorem d_continuous_tri (m : ℕ) (x : Fin (m + 1) → ℂ) :
    Continuous (fun y : UT (m + 2) → ℂ => triXY x y) := by
  unfold triXY
  exact continuous_const.add (G7.continuous_strictUpper _)

theorem d_continuous_red (m : ℕ) (x : Fin (m + 1) → ℂ) :
    Continuous (fun y : UT (m + 2) → ℂ => redOf m (x, y)) := by
  have h : ∀ i j, Continuous (fun y : UT (m + 2) → ℂ => triXY x y i j) := fun i j =>
    (d_continuous_tri m x).matrix_elem i j
  unfold redOf
  exact Continuous.prodMk (h _ _) (Continuous.prodMk (continuous_pi fun k => h _ _)
    (Continuous.prodMk (continuous_pi fun q => h _ _) (continuous_pi fun i => h _ _)))

noncomputable def d_M (m : ℕ) (t : ℂ) (x : Fin (m + 1) → ℂ) (q : ℂ × (UT (m + 2) → ℂ)) : Mat (m + 1 + 1) :=
  Mcoord t (strictUpper (redOf m (x, q.2)).2.2.1) (redOf m (x, q.2)).2.2.2
    (Fin.cons q.1 (redOf m (x, q.2)).2.1) (redOf m (x, q.2)).1

theorem d_continuous_M (m : ℕ) (t : ℂ) (x : Fin (m + 1) → ℂ) : Continuous (d_M m t x) := by
  have hred : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) => redOf m (x, q.2)) :=
    (d_continuous_red m x).comp continuous_snd
  have hX : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) => strictUpper (redOf m (x, q.2)).2.2.1) :=
    (G7.continuous_strictUpper _).comp
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hred)))
  have hB : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) => (redOf m (x, q.2)).2.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hred))
  have hρ : Continuous (fun q : ℂ × (UT (m + 2) → ℂ) =>
      (Fin.cons q.1 (redOf m (x, q.2)).2.1 : Fin (m + 1) → ℂ)) := by
    refine continuous_pi fun k => ?_
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using continuous_fst
    · simp only [Fin.cons_succ]
      exact (continuous_apply k).comp (continuous_fst.comp (continuous_snd.comp hred))
  unfold d_M Mcoord
  exact G7.continuous_blk (continuous_const.matrix_mul (continuous_const.add hX))
    (Continuous.matrix_mulVec continuous_const hB) hρ (continuous_fst.comp hred)

theorem d_MXY_eq (m : ℕ) (D t : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) :
    MXY m D t (x, y) = d_M m t x (rhoXY m D t (x, y), y) := rfl

theorem d_continuous_cutM {s : ℕ} (τ : ℝ) : Continuous (cutM (s := s) τ) := by
  unfold cutM chi0
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  refine Real.smoothTransition.continuous.comp ?_
  have h : Continuous fun Z : Mat s => Z i j := (continuous_apply j).comp (continuous_apply i)
  exact continuous_const.sub ((h.norm.pow 2).div_const _)

theorem d_entries {m : ℕ} (t σ ρ₁ : ℂ) (ρ' : Fin m → ℂ) (x : UT (m + 1) → ℂ) (B : Fin (m + 1) → ℂ) (T : ℝ)
    (hT : 0 ≤ T) (h : ∀ i j, ‖Mcoord t (strictUpper x) B (Fin.cons ρ₁ ρ') σ i j‖ ≤ T) :
    (∀ i j, ‖strictUpper x i j‖ ≤ T) ∧ (∀ i, ‖B i‖ ≤ T) ∧ ‖ρ₁‖ ≤ T ∧ (∀ k, ‖ρ' k‖ ≤ T) ∧ ‖σ‖ ≤ T := by
  obtain ⟨Z, hZd⟩ : ∃ Z : Mat (m + 1 + 1), Z = Mcoord t (strictUpper x) B (Fin.cons ρ₁ ρ') σ := ⟨_, rfl⟩
  have hZ : ‖Z‖ ≤ T := by
    rw [pi_norm_le_iff_of_nonneg hT]
    intro i
    rw [pi_norm_le_iff_of_nonneg hT]
    intro j
    rw [hZd]
    exact h i j
  have hco := (G7.norm_coord_le t σ x B (Fin.cons ρ₁ ρ') Z hZd).trans hZ
  have h1 : ‖(Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ)‖ ≤ T := (norm_fst_le _).trans hco
  have h2 : ‖x‖ ≤ T := ((norm_fst_le _).trans (norm_snd_le _)).trans hco
  have h3 : ‖B‖ ≤ T := ((norm_snd_le _).trans (norm_snd_le _)).trans hco
  refine ⟨fun i j => ?_, fun i => (norm_le_pi_norm B i).trans h3, ?_, fun k => ?_, ?_⟩
  · by_cases hij : i < j
    · simp only [strictUpper, Matrix.of_apply, hij, dif_pos]
      exact (norm_le_pi_norm x _).trans h2
    · simp only [strictUpper, Matrix.of_apply, hij, dif_neg, not_false_iff, norm_zero]
      exact hT
  · simpa using (norm_le_pi_norm (Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ) 0).trans h1
  · simpa using (norm_le_pi_norm (Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ) k.succ).trans h1
  · have := h (Fin.last (m + 1)) (Fin.last (m + 1))
    rwa [Mcoord, G2.blk_ll] at this

theorem d_cutM_entries {s : ℕ} (τ : ℝ) (hτ : 0 < τ) (Z : Mat s) (hne : cutM τ Z ≠ 0) (i j : Fin s) :
    ‖Z i j‖ ≤ 2 * τ := by
  by_contra hlt
  push Not at hlt
  apply hne
  unfold cutM
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  unfold chi0
  apply Real.smoothTransition.zero_of_nonpos
  have h2 : (2 * τ) ^ 2 < ‖Z i j‖ ^ 2 := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg τ]

theorem d_ampCrit_of (hC : CofLowerR) (hDet : DetMXY) : AmpCritContinuous := by
  intro m β Kc hK h0 ε hε hε'
  obtain ⟨t₀, c₀, ht₀, hc₀, hlow⟩ := hC m Kc hK h0 2 (by norm_num)
  refine ⟨t₀, ht₀, ?_⟩
  intro V _ _ _ Φ bd hΦ t D z ht htt hD hz
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hτ0 : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos htn _
  have hred := d_continuous_red m (fun _ => z)
  have hcof : Continuous (fun y : UT (m + 2) → ℂ => cofXY m t (fun _ => z, y)) := by
    unfold cofXY
    exact (G7.continuous_cof m t).comp
      ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hred))).prodMk
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hred))))
  have hthr : 0 < c₀ * ‖t‖ ^ ε := mul_pos hc₀ (Real.rpow_pos_of_pos htn _)
  have hvan : ∀ y : UT (m + 2) → ℂ, ‖cofXY m t (fun _ => z, y)‖ < c₀ * ‖t‖ ^ ε →
      ampIn β m ε Φ D t (fun _ => z, y) = 0 := by
    intro y hy
    by_cases hc : cofXY m t (fun _ => z, y) = 0
    · simp [ampIn, amp, hc]
    · have hcut : cutM (‖t‖ ^ (-ε)) (MXY m D t (fun _ => z, y)) = 0 := by
        by_contra hne
        have hent := d_cutM_entries _ hτ0 _ hne
        obtain ⟨e1, e2, e3, e4, e5⟩ := d_entries t _ _ _ _ _ (2 * ‖t‖ ^ (-ε)) (by positivity) hent
        have hc' : Cof (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2 t ≠ 0 := hc
        have hrel : t ^ (m + 1) * (redOf m (fun _ => z, y)).1 =
            D + Cof (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2 t *
              rhoXY m D t (fun _ => z, y) +
              R0 (strictUpper (redOf m (fun _ => z, y)).2.2.1) (redOf m (fun _ => z, y)).2.2.2
                (redOf m (fun _ => z, y)).2.1 t := by
          rw [rhoXY, rho1, mul_div_cancel₀ _ hc']
          ring
        have := hlow ε hε hε' D hD t ht htt _ _ _ _ _ (G7.isStrictUpper_strictUpper _) e1 e2 e3 e4 e5 hrel
        exact absurd hy (not_lt.2 this)
      simp [ampIn, amp, cutPhi, hcut]
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hc : cofXY m t (fun _ => z, y) = 0
  · have hW : ∀ᶠ y' in 𝓝 y, ‖cofXY m t (fun _ => z, y')‖ < c₀ * ‖t‖ ^ ε :=
      (hcof.norm.continuousAt (x := y)).eventually_lt continuousAt_const (by simpa [hc] using hthr)
    have hE : (fun y' => ampIn β m ε Φ D t (fun _ => z, y')) =ᶠ[𝓝 y] fun _ => (0 : V) :=
      hW.mono fun y' h => hvan y' h
    exact continuousAt_const.congr hE.symm
  · have hrho : ContinuousAt (fun y' : UT (m + 2) → ℂ => rhoXY m D t (fun _ => z, y')) y := by
      unfold rhoXY rho1
      refine ContinuousAt.div ?_ hcof.continuousAt hc
      exact (((continuous_const.mul (continuous_fst.comp hred)).sub continuous_const).sub
        ((G7.continuous_remainder m t).comp (continuous_snd.comp hred))).continuousAt
    have hM : ContinuousAt (fun y' : UT (m + 2) → ℂ => MXY m D t (fun _ => z, y')) y := by
      simp only [d_MXY_eq]
      exact ContinuousAt.comp (f := fun y' : UT (m + 2) → ℂ => (rhoXY m D t (fun _ => z, y'), y'))
        (d_continuous_M m t (fun _ => z)).continuousAt (hrho.prodMk continuousAt_id)
    have hΦc : ContinuousAt Φ (MXY m D t (fun _ => z, y)) :=
      (hΦ _ ⟨D, hD, (hDet m D t _ hc).symm⟩).1.continuousAt
    have hg : ContinuousAt (fun y' : UT (m + 2) → ℂ => gRem m D t (fun _ => z, y')) y := by
      unfold gRem
      exact (hrho.sub continuousAt_const).div_const _
    have hinv : ContinuousAt (fun y' : UT (m + 2) → ℂ => (‖cofXY m t (fun _ => z, y')‖ ^ 2)⁻¹) y :=
      ContinuousAt.inv₀ (hcof.norm.pow 2).continuousAt (by simpa using hc)
    unfold ampIn amp cutPhi
    refine ContinuousAt.smul (ContinuousAt.mul ((G7.continuous_psi β).continuousAt.comp hg)
      (Complex.continuous_ofReal.continuousAt.comp hinv)) (ContinuousAt.smul ?_
        (ContinuousAt.comp (f := fun y' : UT (m + 2) → ℂ => MXY m D t (fun _ => z, y')) hΦc hM))
    exact Complex.continuous_ofReal.continuousAt.comp
      (ContinuousAt.comp (f := fun y' : UT (m + 2) → ℂ => MXY m D t (fun _ => z, y'))
        (d_continuous_cutM _).continuousAt hM)

end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives

namespace Formalism.FourierDecayAlt.P

theorem amplitude_continuous_at_critical : Formalism.FourierDecayAlt.G.AmpCritContinuous :=
  PhaseFunctionDerivatives.d_ampCrit_of cofactor_lower_bound_radius det_matrix_xy

end Formalism.FourierDecayAlt.P

end PartD

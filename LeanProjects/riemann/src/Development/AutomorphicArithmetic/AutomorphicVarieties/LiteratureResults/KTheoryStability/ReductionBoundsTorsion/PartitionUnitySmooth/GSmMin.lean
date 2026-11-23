import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

namespace SmoothMinimalSupport

private theorem rho_one {x : ℝ} (hx : x ≤ 1) : rho x = 1 := by
  unfold rho
  exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]; linarith)

private theorem rho_zero {x : ℝ} (hx : 4 ≤ x) : rho x = 0 := by
  unfold rho
  exact Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]; linarith)

private theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

private theorem chi_lip : ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ,
    |Real.smoothTransition x - Real.smoothTransition y| ≤ K * |x - y| := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
    (s := Set.Icc (0:ℝ) 1) (by simp) (convex_Icc 0 1) isCompact_Icc
  refine ⟨K, K.2, fun x y => ?_⟩
  rw [← Real.smoothTransition.projIcc (x := x), ← Real.smoothTransition.projIcc (x := y)]
  have hp : |(Set.projIcc (0:ℝ) 1 zero_le_one x : ℝ) - Set.projIcc (0:ℝ) 1 zero_le_one y| ≤ |x - y| := by
    have := (LipschitzWith.projIcc (zero_le_one (α := ℝ))).dist_le_mul x y
    simpa [Subtype.dist_eq, Real.dist_eq] using this
  have hq := hK.dist_le_mul _ (Set.projIcc (0:ℝ) 1 zero_le_one x).2 _ (Set.projIcc (0:ℝ) 1 zero_le_one y).2
  rw [Real.dist_eq, Real.dist_eq] at hq
  exact hq.trans (mul_le_mul_of_nonneg_left hp K.2)

private theorem rho_lip : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, |rho a - rho b| ≤ K * |a - b| := by
  obtain ⟨K, hK0, hK⟩ := chi_lip
  refine ⟨K / 3, by positivity, fun a b => ?_⟩
  unfold rho
  refine (hK _ _).trans (le_of_eq ?_)
  rw [show (4 - a) / 3 - (4 - b) / 3 = (b - a) / 3 by ring, abs_div, abs_sub_comm,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  ring

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem qR_zero (h : HS L N) : qR h 0 = 0 := by simp [qR]

private theorem q_zero' (h : HS L N) : q h 0 = 0 := by
  have : toR (0 : Lat L N) = 0 := by funext w a; simp [toR]
  simp [q, this, qR_zero]

private theorem qR_smul (h : HS L N) (z : VR L N) (t : ℝ) : qR h (t • z) = t ^ 2 * qR h z := by
  simp only [qR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (t • z) w = (t : ℂ) • z w := by
    funext a; simp [Complex.real_smul]
  rw [e, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
  ring

private theorem qR_pos {h : HS L N} (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hP : ∀ w, (mat h w).PosDef := hh
  obtain ⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by
    by_contra hc; push Not at hc; exact hz (funext hc)
  have hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ (mat h w *ᵥ z w)).re := fun w =>
    (Complex.nonneg_iff.1 ((hP w).posSemidef.dotProduct_mulVec_nonneg (z w))).1
  have hp : 0 < (star (z w0) ⬝ᵥ (mat h w0 *ᵥ z w0)).re :=
    (Complex.pos_iff.1 ((hP w0).dotProduct_mulVec_pos hw0)).1
  unfold qR
  exact lt_of_lt_of_le hp (Finset.single_le_sum (fun w _ => hnn w) (Finset.mem_univ w0))

private theorem qR_cont {X : Type} [TopologicalSpace X] {f : X → HS L N} {g : X → VR L N}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => qR (f x) (g x) := by
  have hv : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous fun x => (f x).1 w i j :=
    fun w i j => (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_apply w).comp (continuous_subtype_val.comp hf)))
  have hz : ∀ (w : InfinitePlace L) (i : Fin N), Continuous fun x => g x w i :=
    fun w i => (continuous_apply i).comp ((continuous_apply w).comp hg)
  simp only [qR, mat, dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  exact continuous_finsetSum _ fun w _ => Complex.continuous_re.comp (continuous_finsetSum _ fun i _ =>
    ((hz w i).star).mul (continuous_finsetSum _ fun j _ => (hv w i j).mul (hz w j)))

private theorem near {y0 : HS L N} (h0 : y0 ∈ Pos L N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y0, ∀ z : VR L N, |qR y z - qR y0 z| ≤ ε * qR y0 z := by
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere _ _
  have hev : ∀ᶠ y in 𝓝 y0, ∀ u ∈ Metric.sphere (0 : VR L N) 1,
      |qR y u - qR y0 u| < ε * qR y0 u := by
    refine hK.eventually_forall_of_forall_eventually fun u hu => ?_
    have hu0 : u ≠ 0 := by
      rintro rfl; simp at hu
    have hpos : 0 < qR y0 u := qR_pos h0 hu0
    have h1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 := qR_cont continuous_fst continuous_snd
    have h2 : Continuous fun p : HS L N × VR L N => qR y0 p.2 := qR_cont continuous_const continuous_snd
    have hc : Continuous fun p : HS L N × VR L N => |qR p.1 p.2 - qR y0 p.2| - ε * qR y0 p.2 :=
      ((h1.sub h2).abs).sub (continuous_const.mul h2)
    have hneg : (fun p : HS L N × VR L N => |qR p.1 p.2 - qR y0 p.2| - ε * qR y0 p.2) (y0, u) < 0 := by
      simp only [sub_self, abs_zero]; nlinarith
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hneg)] with p hp
    linarith
  filter_upwards [hev] with y hy z
  by_cases hz : z = 0
  · subst hz; simp [qR_zero]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have e : z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    obtain ⟨u, hu', t, ht, e'⟩ : ∃ u ∈ Metric.sphere (0 : VR L N) 1, ∃ t : ℝ, 0 < t ∧ z = t • u :=
      ⟨_, hu, _, hn, e⟩
    have hb := hy _ hu'
    subst e'
    rw [qR_smul, qR_smul, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h2 : 0 < t ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hb.le h2.le
    linarith

private theorem bas (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) :
    0 < lam y ∧ (∀ v : Lat L N, v ≠ 0 → lam y ≤ q y v) ∧ (∃ v : Lat L N, v ≠ 0 ∧ q y v = lam y) ∧
      (∀ B : ℝ, {v : Lat L N | q y v ≤ B}.Finite) ∧ ∀ v, 0 ≤ q y v := by
  obtain ⟨h1, h2, h3, -, h5⟩ := (hB L N hN).1 y hy
  refine ⟨h1, h2, h3, h5, fun v => ?_⟩
  by_cases hv : v = 0
  · rw [hv, q_zero']
  · exact h1.le.trans (h2 v hv)

private theorem zed_supp {y : HS L N} {s : ℝ} (hs : 0 < s) {F : Finset (Lat L N)}
    (hF : ∀ v, q y v < 4 * s → v ∈ F) : zed s y = ∑ v ∈ F, rho (q y v / s) := by
  unfold zed
  refine finsum_eq_sum_of_support_subset _ fun v hv => ?_
  rw [Finset.mem_coe]
  by_contra hc
  refine (Function.mem_support.1 hv) (rho_zero ?_)
  rw [le_div_iff₀ hs]
  by_contra h'
  exact hc (hF v (not_le.1 h'))

private theorem zed_ge (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {s : ℝ} (hs : 0 < s)
    (hl : lam y ≤ s) : 2 ≤ zed s y := by
  classical
  obtain ⟨-, -, ⟨v0, hv0, hq0⟩, hfin, -⟩ := bas hB hN hy
  rw [zed_supp hs (F := (hfin (4 * s)).toFinset ∪ {0, v0})
    (fun v hv => Finset.mem_union_left _ ((hfin _).mem_toFinset.2 (le_of_lt hv)))]
  have hsub : ({0, v0} : Finset (Lat L N)) ⊆ (hfin (4 * s)).toFinset ∪ {0, v0} :=
    Finset.subset_union_right
  calc (2 : ℝ) = ∑ v ∈ ({0, v0} : Finset (Lat L N)), rho (q y v / s) := by
        rw [Finset.sum_pair (Ne.symm hv0), q_zero', zero_div, rho_one (x := 0) (by norm_num),
          rho_one (x := q y v0 / s) (by rw [div_le_one hs]; linarith)]
        norm_num
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => rho_nonneg _)

private theorem zed_eq_one (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {s : ℝ} (hs : 0 < s)
    (hl : 4 * s ≤ lam y) : zed s y = 1 := by
  obtain ⟨-, h2, -, -, -⟩ := bas hB hN hy
  unfold zed
  rw [finsum_eq_single _ (0 : Lat L N) (fun v hv => rho_zero (by rw [le_div_iff₀ hs]; linarith [h2 v hv]))]
  rw [q_zero', zero_div]; exact rho_one (by norm_num)

private theorem zed_inv (hB : Basic) (hN : 1 ≤ N) (γ : Gm L N) (s : ℝ) (y : HS L N) :
    zed s (ac γ y) = zed s y := by
  unfold zed
  simp_rw [(hB L N hN).2.1 γ y]
  exact finsum_comp_equiv (MulAction.toPerm γ⁻¹) (f := fun v => rho (q y v / s))

private def Xk (k : ℤ) (y : HS L N) : ℝ := Real.smoothTransition (zed ((4 : ℝ) ^ k) y - 1)

private def Tk (k : ℤ) (y : HS L N) : ℝ := (4 : ℝ) ^ k * (Xk k y - Xk (k - 1) y)

private def nu (y : HS L N) : ℝ := ∑ᶠ k : ℤ, Tk k y

private theorem four_pos (k : ℤ) : (0:ℝ) < (4:ℝ) ^ k := zpow_pos (by norm_num) k

private theorem Xk_bd (k : ℤ) (y : HS L N) : 0 ≤ Xk k y ∧ Xk k y ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem Xk_one (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {k : ℤ}
    (hl : lam y ≤ (4:ℝ) ^ k) : Xk k y = 1 := by
  unfold Xk
  exact Real.smoothTransition.one_of_one_le (by linarith [zed_ge hB hN hy (four_pos k) hl])

private theorem Xk_zero (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {k : ℤ}
    (hl : (4:ℝ) ^ (k + 1) ≤ lam y) : Xk k y = 0 := by
  unfold Xk
  rw [zpow_add_one₀ (by norm_num : (4:ℝ) ≠ 0)] at hl
  rw [zed_eq_one hB hN hy (four_pos k) (by linarith), sub_self]
  exact Real.smoothTransition.zero

private theorem Tk_supp (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {k : ℤ} (hT : Tk k y ≠ 0) :
    (4:ℝ) ^ (k - 1) < lam y ∧ lam y < (4:ℝ) ^ (k + 1) := by
  have h4 : (1:ℝ) ≤ 4 := by norm_num
  constructor
  · by_contra hc; push Not at hc
    apply hT; unfold Tk
    rw [Xk_one hB hN hy (k := k - 1) hc,
      Xk_one hB hN hy (k := k) (hc.trans (zpow_le_zpow_right₀ h4 (by omega)))]
    ring
  · by_contra hc; push Not at hc
    apply hT; unfold Tk
    rw [Xk_zero hB hN hy (k := k) hc,
      Xk_zero hB hN hy (k := k - 1) (le_trans (zpow_le_zpow_right₀ h4 (by omega)) hc)]
    ring

private theorem Tk_win (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {m k : ℤ}
    (h1 : (4:ℝ) ^ (m - 1) < lam y) (h2 : lam y < (4:ℝ) ^ (m + 2)) (hT : Tk k y ≠ 0) :
    k ∈ Finset.Icc (m - 1) (m + 2) := by
  obtain ⟨a, b⟩ := Tk_supp hB hN hy hT
  have h4 : (1:ℝ) < 4 := by norm_num
  have e1 : m - 1 < k + 1 := (zpow_lt_zpow_iff_right₀ h4).1 (h1.trans b)
  have e2 : k - 1 < m + 2 := (zpow_lt_zpow_iff_right₀ h4).1 (a.trans h2)
  rw [Finset.mem_Icc]; omega

private theorem nu_eq (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) {m : ℤ}
    (h1 : (4:ℝ) ^ (m - 1) < lam y) (h2 : lam y < (4:ℝ) ^ (m + 2)) :
    nu y = ∑ k ∈ Finset.Icc (m - 1) (m + 2), Tk k y := by
  unfold nu
  exact finsum_eq_sum_of_support_subset _ fun k hk => by
    rw [Finset.mem_coe]; exact Tk_win hB hN hy h1 h2 hk

private theorem log_bds {r : ℝ} (hr : 0 < r) : (4:ℝ) ^ Int.log 4 r ≤ r ∧ r < (4:ℝ) ^ (Int.log 4 r + 1) := by
  have a := Int.zpow_log_le_self (b := 4) (by norm_num) hr
  have b := Int.lt_zpow_succ_log_self (b := 4) (by norm_num) r
  push_cast at a b
  exact ⟨a, b⟩

private theorem nu_cmp (hB : Basic) (hN : 1 ≤ N) {y : HS L N} (hy : y ∈ Pos L N) :
    lam y / 4 ≤ nu y ∧ nu y ≤ 4 * lam y := by
  obtain ⟨hl, -⟩ := bas hB hN hy
  obtain ⟨hm1, hm2⟩ := log_bds hl
  set m := Int.log 4 (lam y)
  have h4 : (1:ℝ) < 4 := by norm_num
  have hsupp : ∀ k, Tk k y ≠ 0 → k ∈ ({m, m + 1} : Finset ℤ) := by
    intro k hk
    obtain ⟨a, b⟩ := Tk_supp hB hN hy hk
    have e1 : m < k + 1 := (zpow_lt_zpow_iff_right₀ h4).1 (lt_of_le_of_lt hm1 b)
    have e2 : k - 1 < m + 1 := (zpow_lt_zpow_iff_right₀ h4).1 (a.trans hm2)
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hnu : nu y = Tk m y + Tk (m + 1) y := by
    unfold nu
    rw [finsum_eq_sum_of_support_subset _ (s := {m, m + 1})
      (fun k hk => by rw [Finset.mem_coe]; exact hsupp k hk)]
    rw [Finset.sum_pair (by omega)]
  have x0 : Xk (m - 1) y = 0 := Xk_zero hB hN hy (k := m - 1) (by rw [sub_add_cancel]; exact hm1)
  have x1 : Xk (m + 1) y = 1 := Xk_one hB hN hy (k := m + 1) hm2.le
  have xb := Xk_bd m y
  have e : nu y = (4:ℝ) ^ m * Xk m y + (4:ℝ) ^ (m + 1) * (1 - Xk m y) := by
    rw [hnu]; unfold Tk; rw [x0, add_sub_cancel_right, x1]; ring
  rw [zpow_add_one₀ (by norm_num : (4:ℝ) ≠ 0)] at e hm2
  have hP := four_pos m
  have a1 := mul_le_mul_of_nonneg_left xb.2 hP.le
  have a2 := mul_nonneg hP.le xb.1
  constructor <;> nlinarith

private theorem nu_inv (hB : Basic) (hN : 1 ≤ N) (γ : Gm L N) (y : HS L N) : nu (ac γ y) = nu y := by
  unfold nu Tk Xk
  simp_rw [zed_inv hB hN γ]

private theorem mem_pos_and_lam_mem_Icc_of_cl (hB : Basic) (hN : 1 ≤ N) {y0 y : HS L N} (h0 : y0 ∈ Pos L N) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 2) (hcl : Cl δ y0 y) :
    y ∈ Pos L N ∧ (1 - δ) * lam y0 ≤ lam y ∧ lam y ≤ (1 + δ) * lam y0 := by
  have hyP := ((hB L N hN).2.2.2.1 δ hδ0 hδ y0 h0 y hcl).1
  obtain ⟨-, h2, ⟨v0, hv0, hq0⟩, -, -⟩ := bas hB hN h0
  obtain ⟨-, h2', ⟨v1, hv1, hq1⟩, -, -⟩ := bas hB hN hyP
  have c1 : |q y v1 - q y0 v1| ≤ δ * q y0 v1 := hcl (toR v1)
  have c0 : |q y v0 - q y0 v0| ≤ δ * q y0 v0 := hcl (toR v0)
  rw [abs_le] at c1 c0
  rw [hq0] at c0
  have hqv1 := h2 v1 hv1
  have hqv0 := h2' v0 hv0
  have : (1 - δ) * lam y0 ≤ (1 - δ) * q y0 v1 := mul_le_mul_of_nonneg_left hqv1 (by linarith)
  refine ⟨hyP, ?_, ?_⟩
  · rw [← hq1]; nlinarith
  · nlinarith

private theorem win_of_cl (hB : Basic) (hN : 1 ≤ N) {y0 y : HS L N} (h0 : y0 ∈ Pos L N) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hcl : Cl δ y0 y) :
    y ∈ Pos L N ∧ (4:ℝ) ^ (Int.log 4 (lam y0) - 1) < lam y ∧
      lam y < (4:ℝ) ^ (Int.log 4 (lam y0) + 2) := by
  obtain ⟨hyP, lo, hi⟩ := mem_pos_and_lam_mem_Icc_of_cl hB hN h0 hδ0 hδ hcl
  obtain ⟨hl, -⟩ := bas hB hN h0
  obtain ⟨hm1, hm2⟩ := log_bds hl
  set m := Int.log 4 (lam y0)
  rw [zpow_sub_one₀ (by norm_num : (4:ℝ) ≠ 0)]
  rw [zpow_add_one₀ (by norm_num : (4:ℝ) ≠ 0)] at hm2
  have e2 : (4:ℝ) ^ (m + 2) = (4:ℝ) ^ m * 16 := by
    rw [zpow_add₀ (by norm_num : (4:ℝ) ≠ 0)]; norm_num
  rw [e2]
  have := mul_le_mul_of_nonneg_right hδ hl.le
  have hP := four_pos m
  refine ⟨hyP, by nlinarith, by nlinarith⟩

private theorem cl_refl (y : HS L N) : Cl 0 y y := fun z => by simp

private def qc (v : Lat L N) : HS L N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (UpperTheory.V.KT.ev v)

private theorem qc_apply (v : Lat L N) (y : HS L N) : qc v y = q y v := by
  simp [qc]

private def ZF (F : ℤ → Finset (Lat L N)) (j : ℤ) (y : HS L N) : ℝ :=
  ∑ v ∈ F j, rho (qc v y / (4:ℝ) ^ j)

private def GF (F : ℤ → Finset (Lat L N)) (m : ℤ) (y : HS L N) : ℝ :=
  ∑ k ∈ Finset.Icc (m - 1) (m + 2),
    (4:ℝ) ^ k * (Real.smoothTransition (ZF F k y - 1) - Real.smoothTransition (ZF F (k - 1) y - 1))

private theorem ZF_contDiff (F : ℤ → Finset (Lat L N)) (j : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (ZF F j) := by
  refine ContDiff.sum fun v _ => ?_
  unfold rho
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ((qc v).contDiff.div_const _)).div_const _)

private theorem GF_contDiff (F : ℤ → Finset (Lat L N)) (m : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (GF F m) :=
  ContDiff.sum fun k _ => contDiff_const.mul
    ((Real.smoothTransition.contDiff.comp ((ZF_contDiff F k).sub contDiff_const)).sub
      (Real.smoothTransition.contDiff.comp ((ZF_contDiff F (k - 1)).sub contDiff_const)))

private theorem nu_smooth (hB : Basic) (hN : 1 ≤ N) : ContDiffOn ℝ (⊤ : ℕ∞) (nu : HS L N → ℝ) (Pos L N) := by
  intro y0 h0
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨-, -, -, hfin0, -⟩ := bas hB hN h0
  refine (GF_contDiff (fun j => (hfin0 (8 * (4:ℝ) ^ j)).toFinset) (Int.log 4 (lam y0))).contDiffAt
    |>.congr_of_eventuallyEq ?_
  filter_upwards [near h0 (ε := 1 / 2) (by norm_num)] with y hy
  have hcl : Cl (1 / 2) y0 y := hy
  obtain ⟨hyP, w1, w2⟩ := win_of_cl hB hN h0 (by norm_num) le_rfl hcl
  rw [nu_eq hB hN hyP w1 w2]
  unfold GF
  refine Finset.sum_congr rfl fun k _ => ?_
  have hz : ∀ j : ℤ, zed ((4:ℝ) ^ j) y = ZF (fun j => (hfin0 (8 * (4:ℝ) ^ j)).toFinset) j y := by
    intro j
    rw [zed_supp (four_pos j) (F := (hfin0 (8 * (4:ℝ) ^ j)).toFinset)]
    · simp only [ZF, qc_apply]
    · intro v hv
      rw [Set.Finite.mem_toFinset]
      have c : |q y v - q y0 v| ≤ 1 / 2 * q y0 v := hy (toR v)
      rw [abs_le] at c
      show q y0 v ≤ 8 * (4:ℝ) ^ j
      linarith [c.1]
  simp only [Tk, Xk, hz]

private theorem nu_lip (hB : Basic) (hC : Count) (hN : 1 ≤ N) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → ∀ y ∈ Pos L N, ∀ y' : HS L N,
      Cl δ y y' → |nu y' - nu y| ≤ C * δ * nu y := by
  obtain ⟨Kc, hKc0, hKc⟩ := chi_lip
  obtain ⟨Kr, hKr0, hKr⟩ := rho_lip
  obtain ⟨Cc, hCc0, hCc⟩ := hC L N 256
  have hA0 : 0 ≤ Kc * (Cc * (8 * Kr)) := by positivity
  refine ⟨512 * (Kc * (Cc * (8 * Kr))), by positivity, fun δ hδ0 hδ y hy y' hcl => ?_⟩
  set A := Kc * (Cc * (8 * Kr)) with hA
  obtain ⟨hl, h2, -, hfin, hnn⟩ := bas hB hN hy
  obtain ⟨hm1, -⟩ := log_bds hl
  obtain ⟨-, w1, w2⟩ := win_of_cl hB hN hy le_rfl (by norm_num) (cl_refl y)
  obtain ⟨hy', w1', w2'⟩ := win_of_cl hB hN hy hδ0 hδ hcl
  set m := Int.log 4 (lam y)
  have e16 : (4:ℝ) ^ (m + 2) = 16 * (4:ℝ) ^ m := by
    rw [zpow_add₀ (by norm_num : (4:ℝ) ≠ 0), mul_comm]; norm_num
  have hq : ∀ v, |q y' v - q y v| ≤ δ * q y v := fun v => hcl (toR v)
  have hset : {v : Lat L N | q y v ≤ lam y / 2} = {0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hv; by_contra hne; have := h2 v hne; linarith
    · rintro rfl; rw [q_zero']; positivity
  have hbig : (({v : Lat L N | q y v ≤ 128 * lam y}.ncard : ℕ) : ℝ) ≤ Cc := by
    have := hCc y hy (lam y / 2) (by positivity)
    rw [hset, Set.ncard_singleton, show 256 * (lam y / 2) = 128 * lam y by ring] at this
    simpa using this
  have hcount : ∀ s : ℝ, 8 * s ≤ 128 * lam y → ((hfin (8 * s)).toFinset.card : ℝ) ≤ Cc := by
    intro s hs
    rw [← Set.ncard_eq_toFinset_card _ (hfin _)]
    refine le_trans ?_ hbig
    exact_mod_cast Set.ncard_le_ncard (fun v hv => le_trans hv hs) (hfin _)
  have hX : ∀ j : ℤ, j ≤ m + 2 → |Xk j y' - Xk j y| ≤ A * δ := by
    intro j hj
    unfold Xk
    have hs : 0 < (4:ℝ) ^ j := four_pos j
    have hs16 : (4:ℝ) ^ j ≤ 16 * lam y := by
      have : (4:ℝ) ^ j ≤ (4:ℝ) ^ (m + 2) := zpow_le_zpow_right₀ (by norm_num) hj
      rw [e16] at this; linarith
    have hF : ∀ v, q y v < 4 * (4:ℝ) ^ j → v ∈ (hfin (8 * (4:ℝ) ^ j)).toFinset :=
      fun v hv => (hfin _).mem_toFinset.2 (by show q y v ≤ 8 * (4:ℝ) ^ j; linarith)
    have hF' : ∀ v, q y' v < 4 * (4:ℝ) ^ j → v ∈ (hfin (8 * (4:ℝ) ^ j)).toFinset := by
      intro v hv
      refine (hfin _).mem_toFinset.2 ?_
      show q y v ≤ 8 * (4:ℝ) ^ j
      have c := abs_le.1 (hq v)
      have := mul_le_mul_of_nonneg_right hδ (hnn v)
      linarith [c.1]
    rw [zed_supp hs hF', zed_supp hs hF]
    refine (hKc _ _).trans ?_
    rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    have hterm : ∀ v ∈ (hfin (8 * (4:ℝ) ^ j)).toFinset,
        |rho (q y' v / (4:ℝ) ^ j) - rho (q y v / (4:ℝ) ^ j)| ≤ 8 * Kr * δ := by
      intro v hvF
      have hvq : q y v ≤ 8 * (4:ℝ) ^ j := (hfin _).mem_toFinset.1 hvF
      refine (hKr _ _).trans ?_
      rw [← sub_div, abs_div, abs_of_pos hs]
      have h3 : |q y' v - q y v| / (4:ℝ) ^ j ≤ 8 * δ := by
        rw [div_le_iff₀ hs]
        have := mul_le_mul_of_nonneg_left hvq hδ0
        linarith [hq v]
      calc Kr * (|q y' v - q y v| / (4:ℝ) ^ j) ≤ Kr * (8 * δ) := mul_le_mul_of_nonneg_left h3 hKr0
        _ = 8 * Kr * δ := by ring
    have hc : (((hfin (8 * (4:ℝ) ^ j)).toFinset.card : ℕ) : ℝ) ≤ Cc := hcount _ (by linarith)
    calc Kc * |∑ v ∈ (hfin (8 * (4:ℝ) ^ j)).toFinset, (rho (q y' v / (4:ℝ) ^ j) - rho (q y v / (4:ℝ) ^ j))|
        ≤ Kc * ∑ v ∈ (hfin (8 * (4:ℝ) ^ j)).toFinset, (8 * Kr * δ) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)) hKc0
      _ ≤ A * δ := by
          rw [Finset.sum_const, nsmul_eq_mul, hA]
          have h5 : (((hfin (8 * (4:ℝ) ^ j)).toFinset.card : ℕ) : ℝ) * (8 * Kr * δ) ≤ Cc * (8 * Kr * δ) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          have h6 := mul_le_mul_of_nonneg_left h5 hKc0
          linarith
  have hdiff : nu y' - nu y = ∑ k ∈ Finset.Icc (m - 1) (m + 2), (Tk k y' - Tk k y) := by
    rw [nu_eq hB hN hy' w1' w2', nu_eq hB hN hy w1 w2, Finset.sum_sub_distrib]
  rw [hdiff]
  have hnu := (nu_cmp hB hN hy).1
  calc |∑ k ∈ Finset.Icc (m - 1) (m + 2), (Tk k y' - Tk k y)|
      ≤ ∑ k ∈ Finset.Icc (m - 1) (m + 2), |Tk k y' - Tk k y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (m - 1) (m + 2), (4:ℝ) ^ (m + 2) * (2 * (A * δ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        have e : Tk k y' - Tk k y = (4:ℝ) ^ k * ((Xk k y' - Xk k y) - (Xk (k - 1) y' - Xk (k - 1) y)) := by
          unfold Tk; ring
        rw [e, abs_mul, abs_of_pos (four_pos k)]
        have b1 := abs_le.1 (hX k hk.2)
        have b2 := abs_le.1 (hX (k - 1) (by omega))
        have b3 : |(Xk k y' - Xk k y) - (Xk (k - 1) y' - Xk (k - 1) y)| ≤ 2 * (A * δ) := by
          rw [abs_le]; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
        have b4 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (m + 2) := zpow_le_zpow_right₀ (by norm_num) hk.2
        exact mul_le_mul b4 b3 (abs_nonneg _) (four_pos _).le
    _ = 4 * ((4:ℝ) ^ (m + 2) * (2 * (A * δ))) := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul,
          show (m + 2 + 1 - (m - 1)).toNat = 4 by omega]
        norm_num
    _ ≤ 512 * A * δ * nu y := by
        rw [e16]
        have hAd : 0 ≤ A * δ := mul_nonneg hA0 hδ0
        have k1 := mul_le_mul_of_nonneg_left hm1 hAd
        have k2 := mul_le_mul_of_nonneg_left hnu hAd
        nlinarith

end SmoothMinimalSupport

open SmoothMinimalSupport in
theorem gSmMin : GSmMin := by
  intro hB hC L _ _ N hN
  refine ⟨fun h => nu (dualH h), ?_⟩
  obtain ⟨C, hC0, hlip⟩ := nu_lip (L := L) (N := N) hB hC hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (nu_smooth (L := L) (N := N) hB hN).comp ((hB L N hN).2.2.2.2.2) (fun h hh => ((hB L N hN).1 h hh).2.2.2.1)
  · intro γ h hh
    obtain ⟨γ', hγ'⟩ := (hB L N hN).2.2.1 γ
    simp only [hγ' h hh, nu_inv hB hN]
  · refine ⟨1 / 4, 4, by norm_num, fun h hh => ?_⟩
    have hd := ((hB L N hN).1 h hh).2.2.2.1
    obtain ⟨a, b⟩ := nu_cmp hB hN hd
    unfold lamD
    constructor <;> linarith
  · refine ⟨2 * C, fun δ hδ0 hδ h hh k hk => ?_⟩
    have hd := ((hB L N hN).1 h hh).2.2.2.1
    have hk' := ((hB L N hN).2.2.2.1 δ hδ0 (by linarith) h hh k hk).2
    have := hlip (2 * δ) (by linarith) (by linarith) (dualH h) hd (dualH k) hk'
    calc |nu (dualH k) - nu (dualH h)| ≤ C * (2 * δ) * nu (dualH h) := this
      _ = 2 * C * δ * nu (dualH h) := by ring

end PositivityTheory.KB.SmoothPartitionUnityBasic

end

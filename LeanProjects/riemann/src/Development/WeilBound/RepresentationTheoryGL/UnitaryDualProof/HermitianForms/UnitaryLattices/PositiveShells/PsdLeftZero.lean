import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.ExistsMemBall

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.U.Shell

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem psd_left_zero {V : Type} [AddCommGroup V] [Module ℂ V] {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : IsPsd B) {x : V}
    (hx : B x x = 0) (y : V) : B x y = 0 := by
  set b := B x y with hb
  have hr0 : 0 ≤ (B y y).re := hB.2 y
  have hyx : B y x = starRingEnd ℂ b := hB.1 x y
  set t : ℝ := 1 / ((B y y).re + 1) with ht
  have ht0 : 0 < t := by positivity
  have key := hB.2 (x - ((t : ℂ) * b) • y)
  have e : B (x - ((t : ℂ) * b) • y) (x - ((t : ℂ) * b) • y) =
      B x x - starRingEnd ℂ ((t : ℂ) * b) * b - ((t : ℂ) * b) * B y x +
        ((t : ℂ) * b) * starRingEnd ℂ ((t : ℂ) * b) * B y y := by
    simp only [map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ← hb]
    ring
  have e2 : (B (x - ((t : ℂ) * b) • y) (x - ((t : ℂ) * b) • y)).re =
      (-2 * t + t ^ 2 * (B y y).re) * Complex.normSq b := by
    rw [e, hx, hyx]
    simp only [map_mul, Complex.conj_ofReal, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.normSq_apply]
    ring
  rw [e2] at key
  have htr : t * (B y y).re < 1 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  have hlt : -2 * t + t ^ 2 * (B y y).re < 0 := by nlinarith
  have hN : Complex.normSq b = 0 :=
    le_antisymm (by nlinarith [Complex.normSq_nonneg b]) (Complex.normSq_nonneg b)
  exact Complex.normSq_eq_zero.1 hN

theorem uShell : UShell k := by
  intro ψ _ _ m N h V _ _ π hπ s B hLvl hAtom z c v hz hzv hv
  obtain ⟨hpsd, hkill, hmir⟩ := hLvl
  classical
  set lam : ℝ := nabs k z ^ (((m : ℝ) + 1) * s) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos (nabs_pos k z) _
  by_contra hcon
  push Not at hcon
  have hzv1 : valuation k (z : k) < 1 := by
    by_contra hge
    push Not at hge
    have h1 := (nabs_le_iff (1 : kˣ) z).2 (by simpa using hge)
    have h2 : nabs k (1 : kˣ) = 1 := by simp [nabs]
    linarith
  obtain ⟨w1, hw1, w2, hw2, hw12⟩ := Submodule.mem_sup.1 (derKer_le ψ h π hzv)
  have hgv : π (scalAt k (m + 1) N (by omega) z) v = c • v + (w1 + w2) := by rw [hw12]; abel

  have hP : ∀ y ∈ Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (u : V), w = π (colEl k m N h x) u - u},
      ∃ n : ℕ, ∃ H₀ : AddSubgroup (Fin (m + 1) → k), IsOpen (H₀ : Set (Fin (m + 1) → k)) ∧
        ∀ t, n ≤ t → ∀ H T, IsTr (ball m (z⁻¹ ^ t * 1)) H T → H ≤ H₀ →
          ∑ a ∈ T, π (colEl k m N h a) y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, u, rfl⟩ := hx
      obtain ⟨n, hn⟩ := exists_mem_ball m z hzv1 1 a
      refine ⟨n, stab h π u, isOpen_stab h π hπ u, fun t ht H T hT hH => ?_⟩
      have hfix : FixH h π H u := fun b hb => hH hb
      have ha : a ∈ ball m (z⁻¹ ^ t * 1) := ball_pow_mono m z hzv1 1 ht hn
      simp only [map_sub, Finset.sum_sub_distrib]
      rw [← sum_translate hT hfix ha]
      simp only [pi_colEl_add, sub_self]
    | zero =>
      refine ⟨0, ⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun _ _ _ _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, H₀, hH₀, hx⟩ := hx
      obtain ⟨n', H₀', hH₀', hy⟩ := hy
      refine ⟨max n n', H₀ ⊓ H₀', by rw [AddSubgroup.coe_inf]; exact hH₀.inter hH₀', fun t ht H T hT hH => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      rw [hx t (le_of_max_le_left ht) H T hT (hH.trans inf_le_left),
        hy t (le_of_max_le_right ht) H T hT (hH.trans inf_le_right), add_zero]
    | smul a x _ hx =>
      obtain ⟨n, H₀, hH₀, hx⟩ := hx
      refine ⟨n, H₀, hH₀, fun t ht H T hT hH => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      rw [hx t ht H T hT hH, smul_zero]
  obtain ⟨n₂, H₂, hH₂, hw2P⟩ := hP w2 hw2
  let A : ℕ → AddSubgroup (Fin (m + 1) → k) := fun t => ball m (z⁻¹ ^ (t + n₂) * 1)
  have hA : ∀ t, IsLat (A t) := fun t => isLat_ball m _
  have hAs : ∀ t, scl z (A (t + 1)) = A t := by
    intro t
    show scl z (ball m (z⁻¹ ^ (t + 1 + n₂) * 1)) = ball m (z⁻¹ ^ (t + n₂) * 1)
    rw [scl_ball]
    congr 1
    rw [show t + 1 + n₂ = (t + n₂) + 1 by omega, pow_succ]
    group

  have hR1 : ∀ t, B (avg (1 : AddChar k Circle) h π 0 (A t) (π (scalAt k (m + 1) N (by omega) z) v))
      (π (scalAt k (m + 1) N (by omega) z) v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A t) v) v := by
    intro t
    have hopen : IsOpen ((stab h π v ⊓ stab h π w1 ⊓ stab h π w2 ⊓ H₂ : AddSubgroup (Fin (m + 1) → k)) :
        Set (Fin (m + 1) → k)) := by
      simp only [AddSubgroup.coe_inf]
      exact (((isOpen_stab h π hπ v).inter (isOpen_stab h π hπ w1)).inter (isOpen_stab h π hπ w2)).inter hH₂
    obtain ⟨H, T, hT, hH⟩ := exists_tr (hA t) hopen
    have fv : FixH h π H v := fun b hb => (hH hb).1.1.1
    have fw1 : FixH h π H w1 := fun b hb => (hH hb).1.1.2
    have fw2 : FixH h π H w2 := fun b hb => (hH hb).1.2
    have fw : FixH h π H (w1 + w2) := fun b hb => by rw [map_add, fw1 b hb, fw2 b hb]
    have fgv : FixH h π H (π (scalAt k (m + 1) N (by omega) z) v) := fun b hb => by
      rw [hgv, map_add, map_smul, fv b hb, fw b hb]
    have h2 : avgL h π T w2 = 0 := by
      rw [avgL_apply, hw2P (t + n₂) (by omega) H T hT (fun b hb => (hH hb).2), smul_zero]
    have h1 : avgL h π T w1 ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
      rw [avgL_apply]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => colEl_twKer ψ h π b hw1)
    have hB1 : ∀ y, B (avgL h π T w1) y = 0 := fun y => hkill _ h1 y
    have hB2 : B (avgL h π T v) (w1 + w2) = 0 := by
      rw [B_avgL hmir hT fw, map_add, h2, add_zero, hpsd.1 (avgL h π T w1) v, hB1, map_zero]
    have hQ : avgL h π T (π (scalAt k (m + 1) N (by omega) z) v) = c • avgL h π T v + avgL h π T w1 := by
      rw [hgv, map_add, map_smul, map_add, h2, add_zero]
    have hBs : B (c • avgL h π T v + avgL h π T w1) = c • B (avgL h π T v) + B (avgL h π T w1) := by
      rw [map_add, map_smul]
    rw [avg_eq hT fgv, avg_eq hT fv, hQ, hgv, hBs, LinearMap.add_apply, hB1, add_zero,
      LinearMap.smul_apply, map_add, hB2, add_zero, map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]

  have hR2 : ∀ t, B (avg (1 : AddChar k Circle) h π 0 (A t) (π (scalAt k (m + 1) N (by omega) z) v))
      (π (scalAt k (m + 1) N (by omega) z) v) = (lam : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A (t + 1)) v) v := by
    intro t
    obtain ⟨H, T, hT, hH⟩ := exists_tr (hA (t + 1)) (isOpen_stab h π hπ v)
    have fv : FixH h π H v := fun b hb => hH hb
    rw [← hAs t, avg_eq (hT.smul z) (fv.smul z), avgL_smul, avg_eq hT fv]
    exact B_scalAt h hmir z _ _
  have hrec : ∀ t, (lam : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A (t + 1)) v) v =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * B (avg (1 : AddChar k Circle) h π 0 (A t) v) v :=
    fun t => (hR2 t).symm.trans (hR1 t)
  have hgrow : ∀ t, ‖B (avg (1 : AddChar k Circle) h π 0 (A 0) v) v‖ ≤
      ‖B (avg (1 : AddChar k Circle) h π 0 (A t) v) v‖ := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      refine ih.trans ?_
      have e := congrArg norm (hrec t)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hlam0.le,
        Real.norm_of_nonneg (by positivity)] at e
      nlinarith [norm_nonneg (B (avg (1 : AddChar k Circle) h π 0 (A t) v) v),
        norm_nonneg (B (avg (1 : AddChar k Circle) h π 0 (A (t + 1)) v) v),
        mul_nonneg (sub_nonneg.2 hcon) (norm_nonneg (B (avg (1 : AddChar k Circle) h π 0 (A t) v) v))]

  have htend : Filter.Tendsto (fun t => B (avg (1 : AddChar k Circle) h π 0 (A t) v) v) Filter.atTop (nhds 0) := by
    have := (hAtom v v).comp ((tendsto_ball m z hzv1 1).comp (Filter.tendsto_add_atTop_nat n₂))
    exact this
  have ha0 : B (avg (1 : AddChar k Circle) h π 0 (A 0) v) v = 0 := by
    have hn := htend.norm
    rw [norm_zero] at hn
    exact norm_le_zero_iff.1 (ge_of_tendsto' hn hgrow)
  obtain ⟨H, T, hT, hH⟩ := exists_tr (hA 0) (isOpen_stab h π hπ v)
  have fv : FixH h π H v := fun b hb => hH hb
  rw [avg_eq hT fv] at ha0
  have finv : ∀ b ∈ A 0, π (colEl k m N h b) (avgL h π T v) = avgL h π T v := fun b hb => colEl_avgL hT fv hb
  have fQ : FixH h π H (avgL h π T v) := fun b hb => finv b (hT.1 hb)
  have hQQ : B (avgL h π T v) (avgL h π T v) = 0 := by
    have e1 := B_avgL hmir hT (v := v) fQ
    rw [avgL_of_inv hT finv] at e1
    rw [e1, hpsd.1 (avgL h π T v) v, ha0, map_zero]
  have hker : avgL h π T v ∈ LinearMap.ker B :=
    LinearMap.mem_ker.2 (LinearMap.ext fun y => psd_left_zero hpsd hQQ y)
  exact hv (Submodule.mem_sup.2 ⟨v - avgL h π T v, avgL_sub_mem ψ hT v, avgL h π T v, hker, sub_add_cancel v _⟩)

end PositivityTheory.RgUd.Form.U.Shell

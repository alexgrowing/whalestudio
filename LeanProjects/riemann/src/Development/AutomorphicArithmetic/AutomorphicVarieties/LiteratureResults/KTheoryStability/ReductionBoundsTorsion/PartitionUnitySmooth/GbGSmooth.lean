import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private def gb_g (s : ℝ) : ℝ := 1 / 2 + (s - 1 / 2) * Real.smoothTransition (2 * s - 1)

private theorem actL_mul_apply_eq_actL_actL {L : Type} [Field L] [NumberField L] {N : ℕ} (g g' : Gp L N) (h : HS L N) :
    actL (g * g') h = actL g (actL g' h) := by
  show actM (g * g') h = actM g (actM g' h)
  simp only [actM, LinearMap.coe_mk, AddHom.coe_mk]
  unfold mkHS
  apply Subtype.ext
  funext w i j
  simp only [mat, Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.conjTranspose_mul, Matrix.of_apply]
  rw [show ∀ X : Matrix (Fin N) (Fin N) ℂ, (of fun i j => X i j) = X from fun _ => rfl]
  simp only [Matrix.mul_assoc]

private theorem contDiff_gb_g_and_half_le_and_eq_of_one_le : ContDiff ℝ (↑(⊤ : ℕ∞)) gb_g ∧ (∀ s, 1 / 2 ≤ gb_g s) ∧ ∀ s, 1 ≤ s → gb_g s = s := by
  refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
  · unfold gb_g
    fun_prop
  · unfold gb_g
    by_cases hs : s ≤ 1 / 2
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
      simp
    · have := Real.smoothTransition.nonneg (2 * s - 1)
      nlinarith
  · unfold gb_g
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    ring

private theorem norm_sub_le_two_mul_mul_norm_of_cl (hB : Basic) {L : Type} [Field L] [NumberField L] {N : ℕ} (δ : ℝ) (hδ : 0 ≤ δ)
    (h : HS L N) (hh : h ∈ Pos L N) (k : HS L N) (hk : Cl δ h k) : ‖k - h‖ ≤ 2 * δ * ‖h‖ := by
  have hc : 0 ≤ 2 * δ * ‖h‖ := by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : k = h := Subtype.ext (funext fun w => funext fun i => i.elim0)
    rw [this, sub_self, norm_zero]
    exact hc
  have E := (hB L N hN).2.2.2.2.1 δ hδ h hh k hk
  have hle : ∀ w i, ‖(h : InfinitePlace L → Fin N → Fin N → ℂ) w i i‖ ≤ ‖h‖ := fun w i =>
    ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ i)).trans (norm_le_pi_norm (h : InfinitePlace L → Fin N → Fin N → ℂ) w)
  show ‖((k - h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg hc).2 fun w => (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => ?_
  have e := E w (Pi.single i 1) (Pi.single j 1)
  simp [mat] at e
  have d : ((k - h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) w i j =
      (k : InfinitePlace L → Fin N → Fin N → ℂ) w i j - (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j := rfl
  rw [d]
  have x1 := (Complex.abs_re_le_norm ((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i)).trans (hle w i)
  have y1 := (Complex.abs_re_le_norm ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j)).trans (hle w j)
  have xy : ((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re * ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re ≤ ‖h‖ * ‖h‖ := by
    calc _ ≤ |((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re * ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re| := le_abs_self _
      _ = |((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re| * |((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re| := abs_mul _ _
      _ ≤ ‖h‖ * ‖h‖ := mul_le_mul x1 y1 (abs_nonneg _) (norm_nonneg _)
  have hd := norm_nonneg ((k : InfinitePlace L → Fin N → Fin N → ℂ) w i j - (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j)
  have h4 : 0 ≤ 4 * δ ^ 2 := by positivity
  have e2 : ‖(k : InfinitePlace L → Fin N → Fin N → ℂ) w i j - (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j‖ ^ 2 ≤ (2 * δ * ‖h‖) ^ 2 := by
    calc _ ≤ _ := e
      _ = 4 * δ ^ 2 * (((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re * ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re) := by ring
      _ ≤ 4 * δ ^ 2 * (‖h‖ * ‖h‖) := mul_le_mul_of_nonneg_left xy h4
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ hd hc two_ne_zero).1 e2

theorem pf_GBump : GBump := by
  intro hB hP L _ _ N K hK hKP
  have hPo : IsOpen (Pos L N) := (hP L N).1
  obtain ⟨ε, hε, hεK⟩ := hK.exists_cthickening_subset_open hPo hKP
  have hK'c : IsCompact (Metric.cthickening ε K) := hK.cthickening
  obtain ⟨f, hfs, hfc, hfr⟩ := (Metric.isOpen_thickening (δ := ε) (E := K)).exists_contDiff_support_eq (n := ⊤)
  have f0 : ∀ x, 0 ≤ f x := fun x => (hfr ⟨x, rfl⟩).1
  have f1 : ∀ x, f x ≤ 1 := fun x => (hfr ⟨x, rfl⟩).2
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ f x := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hfc.continuous.continuousOn
      refine ⟨f x0, ?_, fun x hx => hmin hx⟩
      have : x0 ∈ f.support := by rw [hfs]; exact Metric.self_subset_thickening hε K hx0
      exact lt_of_le_of_ne (f0 x0) (Ne.symm this)
  set φ : HS L N → ℝ := fun x => f x / m with hφdef
  have φ0 : ∀ x, 0 ≤ φ x := fun x => div_nonneg (f0 x) hm.le
  have φ1 : ∀ x, φ x ≤ 1 / m := fun x => div_le_div_of_nonneg_right (f1 x) hm.le
  have φK : ∀ x ∈ K, 1 ≤ φ x := fun x hx => (one_le_div hm).2 (hmK x hx)
  have φs : ∀ x, φ x ≠ 0 → x ∈ Metric.cthickening ε K := fun x hx => by
    have : x ∈ f.support := fun h0 => hx (by simp [hφdef, h0])
    rw [hfs] at this
    exact Metric.thickening_subset_cthickening ε K this
  have φc : ContDiff ℝ (↑(⊤ : ℕ∞)) φ := hfc.div_const m
  set τ : Gm L N → HS L N →L[ℝ] HS L N := fun γ => actL ((emb L N γ)⁻¹) with hτ
  have hfin : ∀ B : Set (HS L N), IsCompact B → B ⊆ Pos L N →
      {γ | ∃ h ∈ B, τ γ h ∈ Metric.cthickening ε K}.Finite := by
    intro B hBc hBP
    have F := (hP L N).2 (B ∪ Metric.cthickening ε K) (hBc.union hK'c) (Set.union_subset hBP hεK)
    refine F.inv.subset ?_
    rintro γ ⟨h, hh, hγ⟩
    show ∃ h ∈ _, ac γ⁻¹ h ∈ _
    refine ⟨h, Or.inl hh, Or.inr ?_⟩
    show actL (emb L N γ⁻¹) h ∈ _
    rw [map_inv]
    exact hγ
  set S : HS L N → ℝ := fun h => ∑ᶠ γ, φ (τ γ h) with hS
  have τmul : ∀ γ δ h, τ δ (τ γ h) = τ (γ * δ) h := by
    intro γ δ h
    simp only [hτ]
    rw [← actL_mul_apply_eq_actL_actL, map_mul, _root_.mul_inv_rev]
  have Sinv : ∀ γ h, S (τ γ h) = S h := by
    intro γ h
    simp only [hS, τmul]
    exact finsum_comp_equiv (Equiv.mulLeft γ) (f := fun δ => φ (τ δ h))
  have Sloc : ∀ h0 ∈ Pos L N, ContDiffAt ℝ (↑(⊤ : ℕ∞)) S h0 := by
    intro h0 hh0
    obtain ⟨r, hr, hrP⟩ := Metric.isOpen_iff.1 hPo h0 hh0
    have hBc : IsCompact (Metric.closedBall h0 (r / 2)) := isCompact_closedBall h0 (r / 2)
    have hBP : Metric.closedBall h0 (r / 2) ⊆ Pos L N :=
      (Metric.closedBall_subset_ball (by linarith)).trans hrP
    have heq : ∀ h ∈ Metric.ball h0 (r / 2), S h = ∑ γ ∈ (hfin _ hBc hBP).toFinset, φ (τ γ h) := by
      intro h hh
      apply finsum_eq_sum_of_support_subset
      intro γ hγ
      rw [Set.Finite.coe_toFinset]
      exact ⟨h, Metric.ball_subset_closedBall hh, φs _ hγ⟩
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun h => ∑ γ ∈ (hfin _ hBc hBP).toFinset, φ (τ γ h)) :=
      ContDiff.sum fun γ _ => φc.comp (τ γ).contDiff
    exact hc.contDiffAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (Metric.ball_mem_nhds h0 (by linarith)) heq)
  have Sfin : ∀ h ∈ Pos L N, (Function.support fun γ => φ (τ γ h)).Finite := fun h hh =>
    (hfin {h} isCompact_singleton (by simpa using hh)).subset fun γ hγ => ⟨h, rfl, φs _ hγ⟩
  obtain ⟨gc, g12, gid⟩ := contDiff_gb_g_and_half_le_and_eq_of_one_le
  have gpos : ∀ s, 0 < gb_g s := fun s => lt_of_lt_of_le (by norm_num) (g12 s)
  set ψ : HS L N → ℝ := fun h => φ h / gb_g (S h) with hψ
  have ψc : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ Pos L N
    · exact φc.contDiffAt.div (gc.contDiffAt.comp x (Sloc x hx)) (gpos _).ne'
    · have hxK : x ∉ Metric.cthickening ε K := fun h => hx (hεK h)
      have ev : ψ =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds hxK] with y hy
        have : φ y = 0 := by_contra fun h => hy (φs y h)
        simp [hψ, this]
      exact contDiffAt_const.congr_of_eventuallyEq ev
  have ψ0 : ∀ h, 0 ≤ ψ h := fun h => div_nonneg (φ0 h) (gpos _).le
  have ψb : ∀ h, ψ h ≤ 2 / m := fun h => by
    show φ h / gb_g (S h) ≤ 2 / m
    rw [div_le_iff₀ (gpos _)]
    calc φ h ≤ 1 / m := φ1 h
      _ = 2 / m * (1 / 2) := by ring
      _ ≤ 2 / m * gb_g (S h) := mul_le_mul_of_nonneg_left (g12 _) (by positivity)
  have ψs : ∀ h, ψ h ≠ 0 → h ∈ Metric.cthickening ε K := fun h hh =>
    φs h (fun h0 => hh (by simp [hψ, h0]))
  obtain ⟨Lc, hL⟩ := ψc.lipschitzWith_of_hasCompactSupport
    (HasCompactSupport.intro hK'c fun x hx => by_contra fun h => hx (ψs x h)) (by simp)
  obtain ⟨R, hR⟩ := hK'c.isBounded.exists_norm_le
  set R0 := max R 0 with hR0
  have hR0n : 0 ≤ R0 := le_max_right _ _
  have hLn : (0 : ℝ) ≤ Lc := Lc.2
  have hC : 0 ≤ 16 / m + 4 * Lc * R0 := by positivity
  refine ⟨ψ, Metric.cthickening ε K, 16 / m + 4 * Lc * R0, hK'c, hεK, ψc, ψs, ?_, ?_, ?_⟩
  · intro h
    rw [abs_of_nonneg (ψ0 h)]
    have : 2 / m ≤ 16 / m := by gcongr; norm_num
    linarith [ψb h, show 0 ≤ 4 * (Lc : ℝ) * R0 by positivity]
  · rintro h hh ⟨γ0, hγ0⟩
    have hsupp := Sfin h hh
    have Sge : 1 ≤ S h := by
      have e : τ γ0⁻¹ h = ac γ0 h := by
        simp only [hτ, map_inv, inv_inv]
      calc 1 ≤ φ (τ γ0⁻¹ h) := by rw [e]; exact φK _ hγ0
        _ ≤ S h := single_le_finsum γ0⁻¹ hsupp (fun j => φ0 _)
    have hfun : (fun γ => ψ (actL ((emb L N γ)⁻¹) h)) = fun γ => φ (τ γ h) * (gb_g (S h))⁻¹ := by
      funext γ
      show φ (τ γ h) / gb_g (S (τ γ h)) = _
      rw [Sinv, div_eq_mul_inv]
    rw [hfun, ← finsum_mul, gid _ Sge]
    exact mul_inv_cancel₀ (show S h ≠ 0 by linarith)
  · intro δ hδ h hh k hk
    by_cases hne : ψ k = ψ h
    · rw [hne, sub_self, abs_zero]
      positivity
    have hbd := norm_sub_le_two_mul_mul_norm_of_cl hB δ hδ h hh k hk
    by_cases hδ4 : 1 / 4 ≤ δ
    · have e1 : |ψ k - ψ h| ≤ 2 / m + 2 / m := by
        calc |ψ k - ψ h| ≤ |ψ k| + |ψ h| := abs_sub _ _
          _ ≤ 2 / m + 2 / m := by
            rw [abs_of_nonneg (ψ0 k), abs_of_nonneg (ψ0 h)]
            exact add_le_add (ψb k) (ψb h)
      have e2 : 16 / m * (1 / 4) ≤ 16 / m * δ := mul_le_mul_of_nonneg_left hδ4 (by positivity)
      have e3 : 0 ≤ 4 * (Lc : ℝ) * R0 * δ := by positivity
      have e4 : 2 / m + 2 / m = 16 / m * (1 / 4) := by ring
      nlinarith
    · push_neg at hδ4
      have hnh : ‖h‖ ≤ 2 * R0 := by
        have hor : h ∈ Metric.cthickening ε K ∨ k ∈ Metric.cthickening ε K := by
          by_contra hc
          push_neg at hc
          apply hne
          rw [show ψ k = 0 from by_contra fun H => hc.2 (ψs k H),
            show ψ h = 0 from by_contra fun H => hc.1 (ψs h H)]
        rcases hor with hm' | hm'
        · have := hR h hm'
          have : R ≤ R0 := le_max_left _ _
          linarith
        · have h1 := hR k hm'
          have h2 : R ≤ R0 := le_max_left _ _
          have h3 : ‖h‖ ≤ ‖k‖ + ‖k - h‖ := by
            have := norm_sub_le k (k - h)
            simpa using this
          have h4 : 2 * δ * ‖h‖ ≤ ‖h‖ / 2 := by nlinarith [norm_nonneg h]
          linarith
      have d1 : |ψ k - ψ h| ≤ Lc * ‖k - h‖ := by
        have := hL.dist_le_mul k h
        rwa [Real.dist_eq, dist_eq_norm] at this
      have d2 : (Lc : ℝ) * ‖k - h‖ ≤ Lc * (2 * δ * (2 * R0)) :=
        mul_le_mul_of_nonneg_left (hbd.trans (mul_le_mul_of_nonneg_left hnh (by positivity))) hLn
      have d3 : 0 ≤ 16 / m * δ := by positivity
      nlinarith

end PositivityTheory.KB.SmoothPartitionUnityBasic

end

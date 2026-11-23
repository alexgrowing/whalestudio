import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem sz_fderiv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {f : V → F} {x : V} {b : ℝ} (h : Sz (k + 1) f x b) : Sz k (fderiv ℝ f) x b :=
  fun i hi => by
    rw [norm_iteratedFDeriv_fderiv]
    exact h (i + 1) (Nat.succ_le_succ hi)

private theorem sum_deriv {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {Y : Set V} (hY : IsOpen Y) {y : ℕ → V → F}
    (hy : ∀ j, ContDiffOn ℝ ∞ (y j) Y)
    (hb : ∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j))
    {p : V} (hp : p ∈ Y) :
    Summable (fun j => fderiv ℝ (y j) p) ∧
      HasFDerivAt (fun x => ∑' j, y j x) (∑' j, fderiv ℝ (y j) p) p := by
  obtain ⟨N, hN, b, hs, hle⟩ := hb 1 p hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hN (hY.mem_nhds hp))
  have hpN : p ∈ N := mem_of_mem_nhds hN
  have h1 : ∀ j, ∀ x ∈ N, ‖fderiv ℝ (y j) x‖ ≤ b j := fun j x hx => (sz_fderiv (k := 0) (hle j x hx)).norm_le
  refine ⟨Summable.of_norm_bounded hs fun j => h1 j p hpN, ?_⟩
  refine hasFDerivAt_tsum_of_isPreconnected (u := b) (s := Metric.ball p r) (f := y)
    (f' := fun j x => fderiv ℝ (y j) x) (x₀ := p) hs Metric.isOpen_ball (convex_ball p r).isPreconnected
    (fun j x hx => ?_) (fun j x hx => h1 j x (hball hx).1) (Metric.mem_ball_self hr) ?_ (Metric.mem_ball_self hr)
  · exact (((hy j).contDiffAt (hY.mem_nhds (hball hx).2)).differentiableAt (by simp)).hasFDerivAt
  · exact Summable.of_norm_bounded hs fun j => (hle j p hpN).norm_le

private theorem sum_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (y : ℕ → V → F),
    (∀ j, ContDiffOn ℝ ∞ (y j) Y) →
    (∀ k, ∀ p ∈ Y, ∃ N ∈ 𝓝 p, ∃ b : ℕ → ℝ, Summable b ∧ ∀ j, ∀ x ∈ N, Sz k (y j) x (b j)) →
    ContDiffOn ℝ n (fun x => ∑' j, y j x) Y := by
  induction n with
  | zero =>
    intro F _ _ _ y hy hb
    simp only [CharP.cast_eq_zero, Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (sum_deriv hY hy hb hp).2.continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ y hy hb
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hY]
    refine ⟨fun p hp => (sum_deriv hY hy hb hp).2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h := ih (V →L[ℝ] F) (fun j => fderiv ℝ (y j))
      (fun j => (hy j).fderiv_of_isOpen hY (by simp)) (fun k p hp => by
        obtain ⟨N, hN, b, hs, hle⟩ := hb (k + 1) p hp
        exact ⟨N, hN, b, hs, fun j x hx => sz_fderiv (hle j x hx)⟩)
    exact h.congr fun p hp => (sum_deriv hY hy hb hp).2.fderiv

theorem UpperTheory.V.Lit.Geo.Cs.sumSm :
    SumSm := by
  intro V F _ _ _ _ _ Y hY y hy hb
  refine ⟨contDiffOn_infty.2 fun n => sum_smooth hY n F y hy hb, fun p hp => ?_⟩
  rw [(sum_deriv hY hy hb hp).2.fderiv]
  exact (sum_deriv hY hy hb hp).1.hasSum

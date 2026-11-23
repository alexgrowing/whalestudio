import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ThetaSectionPointwiseNormSqEq

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col ZM

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem zeroMode_pointwise_bound [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (w : Vsp X.dim) (T M : ℝ)
    (hT : ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T)
    (hM : ∀ t, (Col.YB hI hP 1).ptN2 1 (ZM.zmB hI s) t ≤ M) :
    Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T := by
  classical
  choose γ hγL hγ using fun m : Fin (Module.finrank ℝ (IR I)) → ℤ => dual_lift hI m
  obtain ⟨E0, hE0def⟩ : ∃ e : ℝ,
      Real.exp (-Real.pi * ‖uc (IR I) w‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) w‖ ^ 2) = e := ⟨_, rfl⟩
  have hE0 : 0 < E0 := hE0def ▸ Real.exp_pos _

  have hmode : ∀ m, ‖zmC hI s m w‖ * E0 ≤
      Real.sqrt M * Real.exp (-Real.pi * ‖uMap I w - uMap I (-γ m)‖ ^ 2) := by
    intro m
    rw [← hE0def, mode_norm hI hP hs (hγL m) m (hγ m) w]
    have h1 : uMap I w - uMap I (-γ m) = uc (IR I) w + uc (IR I) (γ m) := by
      rw [map_neg, sub_neg_eq_add, uMap_eq_uc, uMap_eq_uc]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hM _)) (Real.exp_pos _).le

  have hinj : Function.Injective (fun m => uMap I (-γ m)) := by
    intro m m' h
    have h' : uc (IR I) (γ m) = uc (IR I) (γ m') := by
      simp only [map_neg, uMap_eq_uc, neg_inj] at h
      exact h
    funext i
    have e1 := hγ m i
    have e2 := hγ m' i
    rw [← Col.inner_uc (K := IR I) (γ m) _ (Ib hI i).2, h',
      Col.inner_uc (K := IR I) (γ m') _ (Ib hI i).2, e2] at e1
    exact_mod_cast e1.symm
  have hfin : ∀ F : Finset (Fin (Module.finrank ℝ (IR I)) → ℤ),
      ∑ m ∈ F, ‖zmC hI s m w‖ * E0 ≤ Real.sqrt M * T := by
    intro F
    calc ∑ m ∈ F, ‖zmC hI s m w‖ * E0
        ≤ ∑ m ∈ F, Real.sqrt M * Real.exp (-Real.pi * ‖uMap I w - uMap I (-γ m)‖ ^ 2) :=
          Finset.sum_le_sum fun m _ => hmode m
      _ = Real.sqrt M * ∑ y ∈ F.image (fun m => uMap I (-γ m)),
            Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.sum_image (fun a _ b _ h => hinj h)]
      _ ≤ Real.sqrt M * T := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply hT
          intro y hy
          obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hy
          exact ⟨-γ m, X.L.neg_mem (hγL m), rfl⟩
  have hsumN : Summable fun m : Fin (Module.finrank ℝ (IR I)) → ℤ => ‖zmC hI s m w‖ := by
    apply summable_of_sum_le (c := Real.sqrt M * T / E0) (fun m => norm_nonneg _)
    intro F
    rw [le_div_iff₀ hE0, Finset.sum_mul]
    exact hfin F

  have hF := tof_torus_inversion (fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => zmG I s (w + tb hI t))
    (fib_continuous hI hs w) (fun x n => fib_periodic hI hs w x n) hsumN.of_norm
  have hF' : HasSum (fun m => zmC hI s m w) (zmG I s w) := by
    have h0 : zmG I s w = zmG I s (w + tb hI 0) := by simp [tb]
    rw [h0]
    exact hF
  have hsq : Real.sqrt (X.ptN2 1 s fun _ => w) = ‖zmG I s w‖ * E0 := by
    rw [thetaSectionPointwiseNormSq_eq hI s w]
    have hexp : Real.exp (-(2 * Real.pi) * ‖uc (IR I) w‖ ^ 2 - Real.pi * ‖p2 (IR I) w‖ ^ 2) =
        E0 ^ 2 := by
      rw [← hE0def, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp, ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) hE0.le)]
  calc Real.sqrt (X.ptN2 1 s fun _ => w) = ‖zmG I s w‖ * E0 := hsq
    _ ≤ (∑' m, ‖zmC hI s m w‖) * E0 := by
        gcongr
        rw [← hF'.tsum_eq]
        exact norm_tsum_le_tsum_norm hsumN
    _ = ∑' m, ‖zmC hI s m w‖ * E0 := tsum_mul_right.symm
    _ ≤ Real.sqrt M * T := (hsumN.mul_right _).tsum_le_of_sum_le hfin

end

end ReciprocityTheory.ChartRestriction.G.I2

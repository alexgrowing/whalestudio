import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

open Matrix Finset Filter Topology Set

noncomputable section

namespace GlobalTheory.CompanionTheory.DSStabLink

open PI.UpqRep CompanionTheory.D.DSIC

theorem flow_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (T : ℝ → (H →L[ℂ] H)) (h0 : ∀ v, T 0 v = v)
    (hadd : ∀ s t v, T (s + t) v = T s (T t v)) (hiso : ∀ t v, ‖T t v‖ = ‖v‖)
    (hder : ∀ w ∈ W, ∃ z ∈ W, HasDerivAt (fun t => T t w) z 0) (u : H) (hu : u ∈ W) :
    T 1 u ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have hQn : ∀ x, ‖Q x‖ ≤ ‖x‖ := fun x => Submodule.norm_starProjection_apply_le _ x
  have hcont : Continuous fun t => T t u := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨z, -, hz⟩ := hder u hu
    have h1 : ContinuousAt (fun s : ℝ => T (s - t) u) t := by
      have h2 : ContinuousAt (fun s : ℝ => s - t) t := by fun_prop
      exact ContinuousAt.comp_of_eq (g := fun t => T t u) hz.continuousAt h2 (by simp)
    have h3 : ContinuousAt (fun s : ℝ => T t (T (s - t) u)) t :=
      (T t).continuous.continuousAt.comp h1
    convert h3 using 2 with s
    rw [← hadd]; simp
  have key : ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → ‖Q (T x u)‖ ≤ 0 := by
    refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => ‖Q (T t u)‖)
      (B := fun _ => 0) (B' := fun _ => 0) ?_ ?_ continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) ?_
    · exact ((Q.continuous.comp hcont).norm).continuousOn
    · simp [h0, hQW u hu]
    · intro x _ r hr
      set w := T x u - Q (T x u) with hw
      obtain ⟨z, hzW, hz⟩ := hder w (hQs _)
      have hg : HasDerivAt (fun t => Q (T t w)) 0 0 := by
        have := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
        simpa [hQW z hzW, Function.comp_def] using this
      have hg2 : HasDerivAt (fun s : ℝ => Q (T (s - x) w)) 0 x := by
        have h2 : HasDerivAt (fun s : ℝ => s - x) 1 x := (hasDerivAt_id x).sub_const x
        have := HasDerivAt.scomp_of_eq (g₁ := fun t => Q (T t w)) x hg h2 (by simp)
        simpa [Function.comp_def] using this
      have hsl := (hasDerivAt_iff_tendsto_slope.1 hg2).norm
      rw [norm_zero] at hsl
      have hev : ∀ᶠ s in 𝓝[>] x, ‖slope (fun s : ℝ => Q (T (s - x) w)) x s‖ < r :=
        (hsl.eventually (gt_mem_nhds hr)).filter_mono (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
      refine (hev.and self_mem_nhdsWithin).frequently.mono ?_
      rintro s ⟨hs, hsx⟩
      have hpos : 0 < s - x := sub_pos.2 hsx
      refine lt_of_le_of_lt ?_ hs
      rw [slope_def_field, slope_def_module, norm_smul, sub_self, h0, hQW w (hQs _), sub_zero,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
      have e : Q (T s u) = Q (T (s - x) w) + Q (T (s - x) (Q (T x u))) := by
        rw [← map_add, ← map_add, hw, sub_add_cancel, ← hadd, sub_add_cancel]
      have e2 : ‖Q (T (s - x) (Q (T x u)))‖ ≤ ‖Q (T x u)‖ := (hQn _).trans (hiso _ _).le
      have e3 := norm_add_le (Q (T (s - x) w)) (Q (T (s - x) (Q (T x u))))
      rw [← e] at e3
      linarith
  have h1 := norm_le_zero_iff.1 (key (x := 1) ⟨zero_le_one, le_rfl⟩)
  simpa [h1] using hQs (T 1 u)

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (c : ℝ → H) (z : H) (hc : ∀ t, c t ∈ W) (hz : HasDerivAt c z 0) :
    z ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have h1 : HasDerivAt (fun t => Q (c t)) (Q z) 0 :=
    (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
  have h2 : (fun t => Q (c t)) = fun _ => 0 := funext fun t => hQW _ (hc t)
  rw [h2] at h1
  have h3 : Q z = 0 := h1.unique (hasDerivAt_const _ _)
  simpa [h3] using hQs z

variable {n : ℕ}

theorem inK_iff (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ (∀ c d, ε c ≠ ε d → X c d = 0) ∧ ∀ c d, star (X d c) = -X c d := by
  unfold inK inG Jm
  simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ∀ c d, ε c ≠ ε d → X c d = 0 := by
      intro c d h
      have := h2 c d
      cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this <;>
        first | linear_combination this / 2 | linear_combination -this / 2
    refine ⟨h3, fun c d => ?_⟩
    have := h1 c d
    by_cases h : ε c = ε d
    · cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this ⊢ <;>
        first | linear_combination this | linear_combination -this
    · simp [h3 c d h, h3 d c (Ne.symm h)]
  · rintro ⟨h1, h2⟩
    constructor
    · intro c d
      by_cases h : ε c = ε d
      · rw [h2, h]; ring
      · simp [h1 c d h, h1 d c (Ne.symm h)]
    · intro c d
      by_cases h : ε c = ε d
      · rw [h]; ring
      · simp [h1 c d h]

theorem inK_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  rw [inK_iff] at hX ⊢
  refine ⟨fun c d h => by simp [hX.1 c d h], fun c d => ?_⟩
  have := hX.2 c d
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', this]
  simp

theorem exp_mem_K (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (inK_smul ε hX t)

theorem exp_mem_UJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem stabLink : KExp → StabLink := by
  intro hK n ε H _ _ σ S E hσ hS U hU
  constructor
  · intro hst g hg v hv
    obtain ⟨X, hX, rfl⟩ := hK n ε g hg
    have := flow_mem (U.map S.subtype) (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)))
      ?_ ?_ ?_ ?_ v hv
    · simpa using this
    · intro v
      simp [hσ.1.1]
    · intro s t v
      have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
      simp only [Complex.ofReal_add, add_smul]
      rw [Matrix.exp_add_of_commute _ _ hc,
        hσ.1.2 _ (exp_mem_UJ ε hX.1 s) _ (exp_mem_UJ ε hX.1 t)]
      rfl
    · intro t v
      exact hσ.2.1 _ (exp_mem_UJ ε hX.1 t) v
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ?_, hS.real X hX.1 w⟩
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      by_cases h : ε a = ε b
      · exact Submodule.smul_mem _ _ ⟨_, hst a b h w hw, rfl⟩
      · simp [((inK_iff ε X).1 hX).1 a b h]
  · intro hst a b hab v hv
    have hL : ∀ X, inK ε X → ∑ c, ∑ d, X c d • (E c d v : H) ∈ U.map S.subtype := fun X hX =>
      deriv_mem _ _ _ (fun t => hst _ (exp_mem_K ε hX t) _ ⟨v, hv, rfl⟩) (hS.real X hX.1 v)
    have hs : ∀ (p q : Fin n) (z : ℂ),
        ∑ c, ∑ d, (Matrix.single p q z) c d • (E c d v : H) = z • (E p q v : H) := by
      intro p q z
      simp [Matrix.single_apply, ite_and]
    have hoff : ∀ (p q : Fin n) (z : ℂ), ε p = ε q → ∀ c d, ε c ≠ ε d →
        Matrix.single p q z c d = 0 := by
      intro p q z h c d hcd
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hcd h
    have hZ : ∀ z : ℂ, z • (E a b v : H) - star z • (E b a v : H) ∈ U.map S.subtype := by
      intro z
      have hin : inK ε (Matrix.single a b z - Matrix.single b a (star z)) := by
        rw [inK_iff]
        refine ⟨fun c d h => by simp [hoff a b z hab c d h, hoff b a _ hab.symm c d h], fun c d => ?_⟩
        simp only [Matrix.sub_apply, Matrix.single_apply, star_sub, apply_ite star, star_star,
          star_zero, neg_sub, and_comm]
      have := hL _ hin
      simpa only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hs] using this
    have h1 := hZ 1
    have h2 := hZ Complex.I
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ (1 / 2 : ℂ) h1)
      (Submodule.smul_mem _ (-Complex.I / 2 : ℂ) h2)
    have e : (1 / 2 : ℂ) • ((1 : ℂ) • (E a b v : H) - star (1 : ℂ) • (E b a v : H)) +
        (-Complex.I / 2 : ℂ) • (Complex.I • (E a b v : H) - star Complex.I • (E b a v : H)) =
        (E a b v : H) := by
      simp only [star_one, Complex.star_def, Complex.conj_I]
      match_scalars
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [e] at h3
    obtain ⟨y, hy, hye⟩ := h3
    have : y = E a b v := Subtype.ext hye
    exact this ▸ hy

end GlobalTheory.CompanionTheory.DSStabLink

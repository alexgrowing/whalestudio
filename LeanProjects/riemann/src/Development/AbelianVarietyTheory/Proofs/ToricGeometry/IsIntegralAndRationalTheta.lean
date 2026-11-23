import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff

namespace GlobalTheory.ThetaRational

section Analytic

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem exists_analytic_leftInverse {Θ : E → W} (hΘ : Differentiable ℂ Θ) {e : E}
    (hinj : Function.Injective (fderiv ℂ Θ e)) :
    ∃ L : W → E, AnalyticAt ℂ L (Θ e) ∧ ∀ᶠ x in 𝓝 e, L (Θ x) = x := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨P, hP⟩ := (fderiv ℂ Θ e : E →ₗ[ℂ] W).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  set P' : W →L[ℂ] E := LinearMap.toContinuousLinearMap P with hP'
  have hd : HasFDerivAt (fun x => P' (Θ x)) ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e := by
    have := P'.hasFDerivAt.comp e (hΘ e).hasFDerivAt
    refine this.congr_fderiv ?_
    ext v
    have := LinearMap.congr_fun hP v
    simpa [hP'] using this
  have hc : ContDiffAt ℂ ω (fun x => P' (Θ x)) e :=
    (P'.contDiff.comp (GlobalTheory.SCV.contDiff_of_differentiable hΘ ω)).contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨fun y => hc.localInverse hd hn (P' y), ?_, ?_⟩
  · exact AnalyticAt.comp (g := hc.localInverse hd hn) (f := P')
      (hc.to_localInverse hd hn).analyticAt (P'.analyticAt _)
  · exact (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse

omit [FiniteDimensional ℂ W] [NormedAddCommGroup W] [NormedSpace ℂ W] in

theorem eq_zero_of_mul_eq_zero {u v : E → ℂ} (hu : Continuous u) (hv : Differentiable ℂ v)
    (hu0 : u ≠ 0) (h : ∀ e, u e ≠ 0 → v e = 0) : v = 0 := by
  obtain ⟨e, he⟩ := Function.ne_iff.1 hu0
  have h1 : v =ᶠ[𝓝 e] 0 := (hu.continuousAt.eventually_ne he).mono h
  have := GlobalTheory.SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hv.differentiableOn
    (differentiableOn_const (0 : ℂ)) (Set.mem_univ e) h1
  exact funext fun x => this (Set.mem_univ x)

end Analytic

section Cone

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {θ : V → W} {f : V → ℂ} {d : ℕ} {Λ K : Set V}

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V] in
theorem exists_rep
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z) (e : ℂ × V) :
    ∃ e' : ℂ × V, e'.2 ∈ K ∧ e'.1 • θ e'.2 = e.1 • θ e.2 ∧ e'.1 ^ d * f e'.2 = e.1 ^ d * f e.2 := by
  obtain ⟨k, hk, hl⟩ := hP e.2
  obtain ⟨κ, -, hκ⟩ := hL _ hl
  obtain ⟨-, h1, h2⟩ := hκ k
  rw [add_sub_cancel] at h1 h2
  refine ⟨(e.1 * κ k, k), hk, ?_, ?_⟩
  · rw [h1, mul_smul]
  · rw [h2, mul_pow, mul_assoc]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V] [NormedSpace ℂ W] in
theorem exists_lower_bound (hK : IsCompact K) (hθ : Continuous θ) (hN : ∀ z, θ z ≠ 0) :
    ∃ ε > 0, ∀ k ∈ K, ε ≤ ‖θ k‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨k, -, hk⟩ := hK.exists_isMinOn hne hθ.norm.continuousOn
  exact ⟨‖θ k‖, norm_pos_iff.2 (hN k), fun x hx => hk hx⟩

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V] in
theorem growth (hK : IsCompact K) (hθ : Continuous θ) (hf : Continuous f) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : ℂ × V, ‖e.1 ^ d * f e.2‖ ≤ C * ‖e.1 • θ e.2‖ ^ d := by
  obtain ⟨ε, hε, hεK⟩ := exists_lower_bound hK hθ hN
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0 / ε ^ d, by positivity, fun e => ?_⟩
  obtain ⟨e', he', h1, h2⟩ := exists_rep hP hL e
  rw [← h1, ← h2, norm_mul, norm_smul, norm_pow, mul_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h3 := (hB _ he').trans (le_max_left B 0)
  have h4 := hεK _ he'
  calc ‖e'.1‖ ^ d * ‖f e'.2‖ * ε ^ d ≤ ‖e'.1‖ ^ d * max B 0 * ‖θ e'.2‖ ^ d := by gcongr
    _ = _ := by ring

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V] in

theorem exists_transl (hN : ∀ z, θ z ≠ 0)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    {e e' : ℂ × V} (he : e.1 • θ e.2 ≠ 0) (h : e'.1 • θ e'.2 = e.1 • θ e.2) :
    ∃ T : ℂ × V → ℂ × V, Continuous T ∧ T e' = e ∧ ∀ x, (T x).1 • θ (T x).2 = x.1 • θ x.2 ∧
      (T x).1 ^ d * f (T x).2 = x.1 ^ d * f x.2 := by
  have ht : e.1 ≠ 0 := left_ne_zero_of_smul he
  have h1 : θ e.2 = (e.1⁻¹ * e'.1) • θ e'.2 := by
    rw [mul_smul, h, inv_smul_smul₀ ht]
  obtain ⟨κ, hκc, hκ⟩ := hL _ (hS _ _ _ h1)
  refine ⟨fun x => (x.1 * (κ x.2)⁻¹, x.2 + (e.2 - e'.2)), ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · exact (continuous_fst.mul ((hκc.comp continuous_snd).inv₀ fun x => (hκ _).1)).prodMk
      (by fun_prop)
  · obtain ⟨h0, h2, -⟩ := hκ e'.2
    rw [add_sub_cancel, h1] at h2
    have h3 := smul_left_injective ℂ (hN e'.2) h2
    refine Prod.ext ?_ (by simp)
    have h4 : e'.1 = e.1 * κ e'.2 := by rw [← h3]; field_simp
    simp only
    rw [h4]
    field_simp
  · obtain ⟨h0, h2, -⟩ := hκ x.2
    simp only
    rw [h2, smul_smul, inv_mul_cancel_right₀ h0]
  · obtain ⟨h0, -, h2⟩ := hκ x.2
    simp only
    rw [h2, mul_pow, inv_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ h0)]

omit [FiniteDimensional ℂ W] in

theorem eventually_mem_image (hK : IsCompact K) (hθ : Continuous θ) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    {e : ℂ × V} (he : e.1 • θ e.2 ≠ 0) {U : Set (ℂ × V)} (hU : U ∈ 𝓝 e) :
    ∀ᶠ y in 𝓝 (e.1 • θ e.2), ∀ x : ℂ × V, x.1 • θ x.2 = y → ∃ x' ∈ U, x'.1 • θ x'.2 = y := by
  obtain ⟨ε, hε, hεK⟩ := exists_lower_bound hK hθ hN
  set Θ : ℂ × V → W := fun x => x.1 • θ x.2 with hΘ
  have hΘc : Continuous Θ := by rw [hΘ]; fun_prop
  set S : Set (ℂ × V) := {x | ∃ x' ∈ U, Θ x' = Θ x} with hSdef
  set M : Set (ℂ × V) := Metric.closedBall (0 : ℂ) ((‖Θ e‖ + 1) / ε) ×ˢ K with hM
  have hMc : IsCompact M := (isCompact_closedBall _ _).prod hK
  have hC : IsClosed (Θ '' (M \ interior S)) := ((hMc.diff isOpen_interior).image hΘc).isClosed
  have hne : Θ e ∈ (Θ '' (M \ interior S))ᶜ := by
    rintro ⟨e', ⟨-, h1⟩, h2⟩
    apply h1
    obtain ⟨T, hTc, hTe, hT⟩ := exists_transl hN hL hS he h2
    rw [mem_interior_iff_mem_nhds]
    have : T ⁻¹' U ∈ 𝓝 e' := hTc.continuousAt.preimage_mem_nhds (by rwa [hTe])
    filter_upwards [this] with x hx using ⟨T x, hx, (hT x).1⟩
  have h5 : ∀ᶠ y in 𝓝 (Θ e), ‖y‖ < ‖Θ e‖ + 1 :=
    continuous_norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [hC.isOpen_compl.mem_nhds hne, h5] with y hy hy' x hx
  obtain ⟨x', hx', h1, -⟩ := exists_rep hP hL x
  have h2 : Θ x' = y := h1.trans hx
  have h3 : x' ∈ M := by
    refine ⟨?_, hx'⟩
    rw [mem_closedBall_zero_iff, le_div_iff₀ hε]
    refine le_trans ?_ hy'.le
    rw [← h2, hΘ]
    simp only [norm_smul]
    gcongr
    exact hεK _ hx'
  have h4 : x' ∈ interior S := by
    by_contra h
    exact hy ⟨x', ⟨h3, h⟩, h2⟩
  obtain ⟨x'', h6, h7⟩ := interior_subset h4
  exact ⟨x'', h6, h7.trans h2⟩

theorem exists_analytic_descent (hK : IsCompact K) (hθ : Differentiable ℂ θ)
    (hf : Differentiable ℂ f) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    (hT : ∀ (z ξ : V) (γ : ℂ), fderiv ℂ θ z ξ = γ • θ z → ξ = 0)
    (e : ℂ × V) (he : e.1 • θ e.2 ≠ 0) :
    ∃ G : W → ℂ, AnalyticAt ℂ G (e.1 • θ e.2) ∧
      ∀ᶠ y in 𝓝 (e.1 • θ e.2), ∀ x : ℂ × V, x.1 • θ x.2 = y → x.1 ^ d * f x.2 = G y := by
  have ht : e.1 ≠ 0 := left_ne_zero_of_smul he
  have hΘ : Differentiable ℂ (fun x : ℂ × V => x.1 • θ x.2) := by fun_prop
  have hh : Differentiable ℂ (fun x : ℂ × V => x.1 ^ d * f x.2) := by fun_prop
  have hinj : Function.Injective (fderiv ℂ (fun x : ℂ × V => x.1 • θ x.2) e) := by
    have h1 := (hasFDerivAt_fst (𝕜 := ℂ) (p := e)).smul
      ((hθ e.2).hasFDerivAt.comp e (hasFDerivAt_snd (𝕜 := ℂ) (p := e)))
    have h2 : fderiv ℂ (fun x : ℂ × V => x.1 • θ x.2) e = _ := h1.fderiv
    rw [h2, injective_iff_map_eq_zero]
    intro v hv
    simp at hv
    have h3 : fderiv ℂ θ e.2 v.2 = (-(e.1⁻¹ * v.1)) • θ e.2 := by
      rw [neg_smul, mul_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_left hv, inv_smul_smul₀ ht]
    have h4 := hT _ _ _ h3
    rw [h4] at hv
    simp [hN] at hv
    exact Prod.ext hv h4
  obtain ⟨L, hLa, hLe⟩ := exists_analytic_leftInverse hΘ hinj
  refine ⟨fun y => (L y).1 ^ d * f (L y).2, ?_, ?_⟩
  · exact AnalyticAt.comp (g := fun x : ℂ × V => x.1 ^ d * f x.2) (f := L)
      (GlobalTheory.SCV.analyticOnNhd_of_differentiable hh Set.univ _ trivial) hLa
  · filter_upwards [eventually_mem_image hK hθ.continuous hN hP hL hS he hLe,
      eventually_ne_nhds he] with y hy hy0 x hx
    obtain ⟨x', h1, h2⟩ := hy x hx
    obtain ⟨T, -, hTe, hT⟩ := exists_transl hN hL hS (e := x') (e' := x) (h2 ▸ hy0)
      (hx.trans h2.symm)
    have h3 : L y = x' := h2 ▸ h1
    rw [h3, ← (hT x).2, hTe]

end Cone

section Algebra

variable {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ}

theorem algHom_eval₂ (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (χ : A →ₐ[ℂ] ℂ)
    (r : Polynomial (MvPolynomial (Fin n) ℂ)) (a : A) :
    χ (r.eval₂ j.toRingHom a) =
      (r.map (MvPolynomial.eval fun i => χ (j (MvPolynomial.X i)))).eval (χ a) := by
  rw [Polynomial.eval_map]
  have := Polynomial.hom_eval₂ r j.toRingHom χ.toRingHom a
  refine this.trans ?_
  congr 1
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => by simp)
  rw [MvPolynomial.eval_C]
  exact (χ.comp j).commutes c

theorem algHom_apply_mv (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (χ : A →ₐ[ℂ] ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    χ (j q) = MvPolynomial.eval (fun i => χ (j (MvPolynomial.X i))) q := by
  simpa using algHom_eval₂ j χ (Polynomial.C q) 0

theorem exists_algHom (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (a : A)
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (q : MvPolynomial (Fin n) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin n) ℂ), r.eval₂ j.toRingHom a = 0 → p ∣ r)
    (hq : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin n) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (w : (Fin n → ℂ) × ℂ) (hw : MvPolynomial.eval w.1 q ≠ 0)
    (hw' : (p.map (MvPolynomial.eval w.1)).eval w.2 = 0) :
    ∃ χ : A →ₐ[ℂ] ℂ, (∀ i, χ (j (MvPolynomial.X i)) = w.1 i) ∧ χ a = w.2 := by
  choose R hR using hq
  set ρ := Polynomial.eval₂RingHom (MvPolynomial.eval w.1) w.2 with hρ
  set ψ := Polynomial.eval₂RingHom j.toRingHom a with hψ
  have hR' : ∀ b, ψ (R b) = j q * b := fun b => (hR b).symm
  have hψq : ψ (Polynomial.C q) = j q := by simp [hψ]
  have hρq : ρ (Polynomial.C q) = MvPolynomial.eval w.1 q := by simp [hρ]
  have hρp : ρ p = 0 := by rw [Polynomial.eval_map] at hw'; exact hw'
  have key : ∀ r r', ψ r = ψ r' → ρ r = ρ r' := by
    intro r r' h
    have h1 : ψ (r - r') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨s, hs⟩ := hp _ h1
    rw [← sub_eq_zero, ← map_sub, hs, map_mul, hρp, zero_mul]
  have key2 : ∀ r, ρ (R (ψ r)) / MvPolynomial.eval w.1 q = ρ r := by
    intro r
    rw [div_eq_iff hw, key (R (ψ r)) (r * Polynomial.C q) (by rw [hR', map_mul, hψq, mul_comm]),
      map_mul, hρq]
  let χ : A →ₐ[ℂ] ℂ :=
    { toFun := fun b => ρ (R b) / MvPolynomial.eval w.1 q
      map_one' := by simpa using key2 1
      map_zero' := by simpa using key2 0
      map_add' := fun b b' => by
        rw [← add_div, ← map_add, key (R (b + b')) (R b + R b') (by
          rw [map_add, hR', hR', hR', mul_add])]
      map_mul' := fun b b' => by
        have := key (Polynomial.C q * R (b * b')) (R b * R b') (by
          rw [map_mul, map_mul, hR', hR', hR', hψq]; ring)
        rw [map_mul, map_mul, hρq] at this
        field_simp
        rw [← this, mul_comm]
      commutes' := fun c => by
        have h1 : ψ (Polynomial.C (MvPolynomial.C c)) = algebraMap ℂ A c := by
          rw [hψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
          exact j.commutes c
        rw [← h1, key2]
        simp [hρ] }
  refine ⟨χ, fun i => ?_, ?_⟩
  · have h1 : ψ (Polynomial.C (MvPolynomial.X i)) = j (MvPolynomial.X i) := by simp [hψ]
    change ρ (R _) / _ = _
    rw [← h1, key2]
    simp [hρ]
  · have h1 : ψ Polynomial.X = a := by simp [hψ]
    change ρ (R _) / _ = _
    rw [← h1, key2]
    simp [hρ]

end Algebra

section Growth

variable {E : Type*} {n : ℕ}

theorem growth_mv (q : MvPolynomial (Fin n) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin n → ℂ, ‖MvPolynomial.eval x q‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction q using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add p q hp hq =>
    obtain ⟨C, m, hC, h⟩ := hp
    obtain ⟨C', m', hC', h'⟩ := hq
    refine ⟨C + C', m + m', by positivity, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by simp
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((h x).trans ?_) ((h' x).trans ?_))
    · gcongr; omega
    · gcongr; omega
  | mul_X p i hp =>
    obtain ⟨C, m, hC, h⟩ := hp
    refine ⟨C, m + 1, hC, fun x => ?_⟩
    rw [map_mul, norm_mul, MvPolynomial.eval_X, pow_succ, ← mul_assoc]
    have := norm_le_pi_norm x i
    have := h x
    gcongr
    linarith

theorem growth_finite {ι : Type*} [Fintype ι] (x : E → ℝ) (hx : ∀ e, 1 ≤ x e) (u : ι → E → ℂ)
    (hu : ∀ c, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ e, ‖u c e‖ ≤ C * x e ^ m) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ e c, ‖u c e‖ ≤ C * x e ^ m := by
  choose C m hC h using hu
  refine ⟨∑ c, C c, ∑ c, m c, Finset.sum_nonneg fun c _ => hC c, fun e c => (h c e).trans ?_⟩
  have h1 : C c ≤ ∑ c, C c := Finset.single_le_sum (fun c _ => hC c) (Finset.mem_univ c)
  have h2 : m c ≤ ∑ c, m c := Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ c)
  have := hx e
  have := hC c
  have := this.trans h1
  gcongr

theorem growth_root (s : Polynomial (MvPolynomial (Fin n) ℂ)) (hs : s.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin n → ℂ) (y : ℂ),
      (s.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  obtain ⟨C, m, hC, h⟩ := growth_finite (ι := Fin s.natDegree) (fun x : Fin n → ℂ => 1 + ‖x‖)
    (fun x => by simp) (fun c x => MvPolynomial.eval x (s.coeff c)) fun c => growth_mv _
  refine ⟨C + 1, m, by positivity, fun x y hy => ?_⟩
  have hm := hs.map (MvPolynomial.eval x)
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hm.ne_zero hy
  have h0 : (0 : ℝ) ≤ C * (1 + ‖x‖) ^ m := by positivity
  have h2 : (s.map (MvPolynomial.eval x)).cauchyBound ≤ ⟨_, h0⟩ + 1 := by
    rw [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hs.natDegree_map]
    refine add_le_add ?_ le_rfl
    refine Finset.sup_le fun i hi => ?_
    rw [Polynomial.coeff_map]
    exact h x ⟨i, Finset.mem_range.1 hi⟩
  have h3 : ‖y‖ ≤ C * (1 + ‖x‖) ^ m + 1 := by exact_mod_cast (h1.le.trans h2)
  have h4 : (1 : ℝ) ≤ (1 + ‖x‖) ^ m := one_le_pow₀ (by simp)
  linarith

theorem analyticAt_eval (r : Polynomial (MvPolynomial (Fin n) ℂ)) (w : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin n → ℂ) × ℂ => (r.map (MvPolynomial.eval w.1)).eval w.2) w := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.map_add, Polynomial.eval_add] using hp.fun_add hq
  | monomial k c =>
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial]
    refine AnalyticAt.fun_mul ?_ (analyticAt_snd.fun_pow k)
    exact AnalyticAt.aeval_mvPolynomial (A := ℂ) (f := fun w : (Fin n → ℂ) × ℂ => w.1)
      (fun i => ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).analyticAt w) c

end Growth

section Core

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]

omit [FiniteDimensional ℂ E] [Fintype ι] in
theorem differentiable_of_mem_adjoin {u : ι → E → ℂ} (hu : ∀ c, Differentiable ℂ (u c))
    {b : E → ℂ} (hb : b ∈ Algebra.adjoin ℂ (Set.range u)) : Differentiable ℂ b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨c, rfl⟩ := hx; exact hu c
  | algebraMap r => exact differentiable_const r
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι] in

theorem exists_eval_eq {u : ι → E → ℂ}
    (hcl : ∀ y : ι → ℂ, (∀ F : MvPolynomial ι ℂ, (∀ e, MvPolynomial.eval (fun c => u c e) F = 0) →
      MvPolynomial.eval y F = 0) → ∃ e, y = fun c => u c e)
    (χ : Algebra.adjoin ℂ (Set.range u) →ₐ[ℂ] ℂ) : ∃ e, ∀ b, χ b = b.1 e := by
  set g : ι → Algebra.adjoin ℂ (Set.range u) := fun c => ⟨u c, Algebra.subset_adjoin ⟨c, rfl⟩⟩
    with hg
  obtain ⟨e, he⟩ := hcl (fun c => χ (g c)) fun F hF => by
    have h1 : MvPolynomial.aeval g F = 0 := by
      refine Subtype.ext (funext fun e => ?_)
      have := (fun φ g F => (MvPolynomial.comp_aeval_apply (R := ℂ) g φ F).symm)
        ((Pi.evalAlgHom ℂ (fun _ : E => ℂ) e).comp (Algebra.adjoin ℂ (Set.range u)).val) g F
      exact this.symm.trans (hF e)
    have := (fun φ g F => (MvPolynomial.comp_aeval_apply (R := ℂ) g φ F).symm) χ g F
    rw [h1, map_zero] at this
    exact this
  refine ⟨e, fun ⟨b, hb⟩ => ?_⟩
  induction hb using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨c, rfl⟩ := hx; exact congrFun he c
  | algebraMap r => exact χ.commutes r
  | add x y hx' hy' hx hy => exact (map_add χ ⟨x, hx'⟩ ⟨y, hy'⟩).trans (by rw [hx, hy])
  | mul x y hx' hy' hx hy => exact (map_mul χ ⟨x, hx'⟩ ⟨y, hy'⟩).trans (by rw [hx, hy])

theorem isIntegral_and_rational
    (hnoeth : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a))
    (hrat : (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map (MvPolynomial.eval z.1)).eval z.2))
    {u : ι → E → ℂ} {h : E → ℂ} (hu : ∀ c, Differentiable ℂ (u c)) (hh : Differentiable ℂ h)
    (hcl : ∀ y : ι → ℂ, (∀ F : MvPolynomial ι ℂ, (∀ e, MvPolynomial.eval (fun c => u c e) F = 0) →
      MvPolynomial.eval y F = 0) → ∃ e, y = fun c => u c e)
    {c₀ : ι} (hc₀ : u c₀ ≠ 0)
    (hdesc : ∀ e, (fun c => u c e) ≠ 0 → ∃ G : (ι → ℂ) → ℂ, AnalyticAt ℂ G (fun c => u c e) ∧
      ∀ᶠ y in 𝓝 (fun c => u c e), ∀ x, (fun c => u c x) = y → h x = G y)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C) (hgr : ∀ e, ‖h e‖ ≤ C * ‖fun c => u c e‖ ^ m) :
    IsIntegral (Algebra.adjoin ℂ (Set.range u)) h ∧
      ∃ a ∈ Algebra.adjoin ℂ (Set.range u), ∃ b ∈ Algebra.adjoin ℂ (Set.range u),
        b ≠ 0 ∧ b * h = a := by
  set A := Algebra.adjoin ℂ (Set.range u) with hA
  have hd : ∀ b : A, Differentiable ℂ b.1 := fun b => differentiable_of_mem_adjoin hu b.2
  have : NoZeroDivisors A := ⟨fun {b b'} hb => by
    by_cases h0 : b = 0
    · exact Or.inl h0
    refine Or.inr (Subtype.ext (eq_zero_of_mul_eq_zero (hd b).continuous (hd b')
      (fun h1 => h0 (Subtype.ext h1)) fun e he => ?_))
    exact (mul_eq_zero.1 (congrFun (congrArg Subtype.val hb) e)).resolve_left he⟩
  have : IsDomain A := NoZeroDivisors.to_isDomain A
  have : Algebra.FiniteType ℂ A := .adjoin_of_finite (Set.finite_range u)
  obtain ⟨n, j, a, p, q₀, -, hj, hfin, hpm, -, hp, hq₀, hq₀p, hq₀b⟩ := hnoeth A
  set g : ι → A := fun c => ⟨u c, Algebra.subset_adjoin ⟨c, rfl⟩⟩ with hg
  have hint : ∀ b : A, j.toRingHom.IsIntegralElem b := hfin.to_isIntegral

  obtain ⟨q₁, hq₁, b₁, hb₁⟩ : ∃ q₁ : MvPolynomial (Fin n) ℂ, q₁ ≠ 0 ∧ ∃ b₁, j q₁ = b₁ * g c₀ := by
    letI := j.toRingHom.toAlgebra
    have h1 := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin n) ℂ) (x := g c₀)
      (I := Ideal.span {g c₀}) (fun h => hc₀ (congrArg Subtype.val h))
      (Ideal.mem_span_singleton_self _) (hint _)
    obtain ⟨q₁, h2, h3⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    obtain ⟨b₁, h4⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 h2)
    exact ⟨q₁, h3, b₁, h4.symm⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = q₁ * q₀ := ⟨_, rfl⟩
  have hq : q ≠ 0 := hqdef ▸ mul_ne_zero hq₁ hq₀
  have hqp : Polynomial.C q ∈ Ideal.span {p, p.derivative} := by
    rw [hqdef, map_mul]
    exact Ideal.mul_mem_left _ _ hq₀p
  have hqb : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin n) ℂ),
      j q * b = r.eval₂ j.toRingHom a := by
    intro b
    obtain ⟨r, hr⟩ := hq₀b (j q₁ * b)
    exact ⟨r, by rw [← hr, hqdef, map_mul]; ring⟩
  let ev : E → A →ₐ[ℂ] ℂ := fun e => (Pi.evalAlgHom ℂ (fun _ : E => ℂ) e).comp A.val
  have hev : ∀ e (b : A), ev e b = b.1 e := fun _ _ => rfl
  let x : E → Fin n → ℂ := fun e i => ev e (j (MvPolynomial.X i))
  let pr : E → (Fin n → ℂ) × ℂ := fun e => (x e, ev e a)
  have hx : ∀ e s, ev e (j s) = MvPolynomial.eval (x e) s := fun e s => algHom_apply_mv j (ev e) s
  have hpr : ∀ e (r : Polynomial (MvPolynomial (Fin n) ℂ)) (b : A), ev e (r.eval₂ j.toRingHom b) =
      (r.map (MvPolynomial.eval (x e))).eval (ev e b) := fun e r b => algHom_eval₂ j (ev e) r b
  set Z : Set ((Fin n → ℂ) × ℂ) := {z : (Fin n → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
    (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} with hZ
  have hprZ : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → pr e ∈ Z := fun e he =>
    ⟨he, by rw [← hpr, (hp p).2 dvd_rfl, map_zero]⟩
  have hsurj : ∀ w ∈ Z, ∃ e, pr e = w := by
    intro w hw
    obtain ⟨χ, h1, h2⟩ := exists_algHom j a p q (fun r => (hp r).1) hqb w hw.1 hw.2
    obtain ⟨e, he⟩ := exists_eval_eq hcl χ
    exact ⟨e, Prod.ext (funext fun i => (he _).symm.trans (h1 i)) ((he _).symm.trans h2)⟩
  choose R hR using fun c => hqb (g c)
  let ρ : (Fin n → ℂ) × ℂ → ι → ℂ := fun w c =>
    ((R c).map (MvPolynomial.eval w.1)).eval w.2 / MvPolynomial.eval w.1 q
  have hρ : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → (fun c => u c e) = ρ (pr e) := by
    intro e he
    funext c
    change _ = ((R c).map (MvPolynomial.eval (x e))).eval (ev e a) / MvPolynomial.eval (x e) q
    rw [eq_div_iff he, ← hpr, ← hR, map_mul, hx, mul_comm]
    rfl
  have hne : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → (fun c => u c e) ≠ 0 := by
    intro e he h0
    apply he
    have : ev e (g c₀) = 0 := congrFun h0 c₀
    rw [hqdef, map_mul, ← hx e q₁, hb₁, map_mul, this, mul_zero, zero_mul]
  classical
  let φ : (Fin n → ℂ) × ℂ → ℂ := fun w => h (Function.invFun pr w)
  have hinv : ∀ w ∈ Z, pr (Function.invFun pr w) = w := fun w hw => Function.invFun_eq (hsurj w hw)
  have hinv' : ∀ w ∈ Z, MvPolynomial.eval (x (Function.invFun pr w)) q ≠ 0 := by
    intro w hw
    have : x (Function.invFun pr w) = w.1 := congrArg Prod.fst (hinv w hw)
    rw [this]
    exact hw.1
  have hφ : ∀ e, MvPolynomial.eval (x e) q ≠ 0 → φ (pr e) = h e := by
    intro e he
    obtain ⟨G, -, hG⟩ := hdesc e (hne e he)
    have hG' := hG.self_of_nhds
    rw [hG' e rfl]
    refine hG' _ ?_
    rw [hρ _ (hinv' _ (hprZ e he)), hinv _ (hprZ e he), hρ e he]
  obtain ⟨C', m', hC', hgr'⟩ := growth_finite (fun e => 1 + ‖x e‖) (fun e => by simp) u fun c => by
    obtain ⟨s, hs, hs'⟩ := hint (g c)
    obtain ⟨C', m', hC', h1⟩ := growth_root s hs
    exact ⟨C', m', hC', fun e => h1 (x e) (ev e (g c)) (by rw [← hpr, hs', map_zero])⟩
  obtain ⟨⟨s, hs, hs'⟩, r, hr⟩ := hrat n (m' * m) p q φ (C * C' ^ m) hpm hq hqp
    (fun w hw => by
      obtain ⟨e, rfl⟩ := hsurj w hw
      obtain ⟨G, hGa, hG⟩ := hdesc e (hne e hw.1)
      rw [hρ e hw.1] at hGa hG
      have hρa : AnalyticAt ℂ ρ (pr e) := by
        refine analyticAt_pi_iff.2 fun c => (analyticAt_eval (R c) _).fun_div ?_ hw.1
        simpa using analyticAt_eval (Polynomial.C q) (pr e)
      refine ⟨G ∘ ρ, hGa.comp hρa, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (hρa.continuousAt.eventually hG), self_mem_nhdsWithin]
        with w h1 h2
      refine h1 _ ?_
      rw [hρ _ (hinv' _ h2), hinv _ h2])
    (fun w hw => by
      obtain ⟨e, rfl⟩ := hsurj w hw
      rw [hφ e hw.1]
      refine (hgr e).trans ?_
      have h1 : ‖fun c => u c e‖ ≤ C' * (1 + ‖x e‖) ^ m' :=
        (pi_norm_le_iff_of_nonneg (by positivity)).2 (hgr' e)
      rw [mul_assoc, pow_mul, ← mul_pow]
      gcongr)
  have hjq : j q ≠ 0 := fun h0 => hq (hj (h0.trans (map_zero j).symm))
  constructor
  · refine ⟨s.map j.toRingHom, hs.map _, ?_⟩
    have h1 : ∀ e, Polynomial.eval₂ (algebraMap A (E → ℂ)) h (s.map j.toRingHom) e =
        (s.map (MvPolynomial.eval (x e))).eval (h e) := by
      intro e
      have := Polynomial.hom_eval₂ (s.map j.toRingHom) (algebraMap A (E → ℂ))
        (Pi.evalRingHom (fun _ : E => ℂ) e) h
      refine this.trans ?_
      rw [Polynomial.eval₂_map, Polynomial.eval_map]
      congr 1
      exact RingHom.ext fun s => hx e s
    refine eq_zero_of_mul_eq_zero (hd (j q)).continuous ?_ (fun h0 => hjq (Subtype.ext h0))
      fun e he => ?_
    · rw [funext h1]
      intro e
      have h2 : Differentiable ℂ (fun e => (x e, h e)) :=
        (differentiable_pi.2 fun i => hd _).prodMk hh
      exact (analyticAt_eval s (x e, h e)).differentiableAt.comp e (h2 e)
    · rw [← hev, hx] at he
      rw [h1, ← hφ e he]
      exact hs' _ (hprZ e he)
  · refine ⟨(j q * r.eval₂ j.toRingHom a).1, Subtype.prop _,
      (j q * p.derivative.eval₂ j.toRingHom a).1, Subtype.prop _, fun h0 => ?_, funext fun e => ?_⟩
    · have h1 : p.derivative.eval₂ j.toRingHom a = 0 :=
        (mul_eq_zero.1 (Subtype.ext h0 : j q * _ = 0)).resolve_left hjq
      obtain ⟨α, β, h2⟩ := Ideal.mem_span_pair.1 hqp
      have h3 := congrArg (Polynomial.eval₂ j.toRingHom a) h2
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, h1,
        (hp p).2 dvd_rfl, Polynomial.eval₂_C] at h3
      exact hjq (by simpa using h3.symm)
    · rw [Pi.mul_apply, ← hev, ← hev, map_mul, map_mul, hx, hpr, hpr, mul_assoc]
      by_cases he : MvPolynomial.eval (x e) q = 0
      · rw [he, zero_mul, zero_mul]
      · rw [← hφ e he]
        congr 1
        exact hr _ (hprZ e he)

end Core

theorem exists_compact_reps {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (h : Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤) :
    ∃ K : Set (Fin g → ℂ), IsCompact K ∧
      ∀ z, ∃ k ∈ K, z - k ∈ (periodLattice τ : Set (Fin g → ℂ)) := by
  let Φ : (Fin g → ℝ) × (Fin g → ℝ) → Fin g → ℂ := fun v => τ *ᵥ ofRealVec v.1 + ofRealVec v.2
  have hΦ : Continuous Φ := by
    have h1 : Continuous (ofRealVec : (Fin g → ℝ) → Fin g → ℂ) := by
      unfold ofRealVec; fun_prop
    exact (continuous_const.matrix_mulVec (h1.comp continuous_fst)).add (h1.comp continuous_snd)
  have hadd : ∀ v w, Φ (v + w) = Φ v + Φ w := by
    intro v w
    have h1 : ∀ a b : Fin g → ℝ, ofRealVec (a + b) = ofRealVec a + ofRealVec b := fun a b => by
      ext i; simp [ofRealVec]
    simp only [Φ, Prod.fst_add, Prod.snd_add, h1, Matrix.mulVec_add]
    abel
  have hsmul : ∀ (r : ℝ) v, Φ (r • v) = r • Φ v := by
    intro r v
    have h1 : ∀ a : Fin g → ℝ, ofRealVec (r • a) = r • ofRealVec a := fun a => by
      ext i; simp [ofRealVec]
    simp only [Φ, Prod.smul_fst, Prod.smul_snd, h1, Matrix.mulVec_smul, smul_add]
  have hint : ∀ n n' : Fin g → ℤ,
      Φ (fun i => n i, fun i => n' i) = τ *ᵥ ofIntVec n + ofIntVec n' := by
    intro n n'
    have h1 : ∀ a : Fin g → ℤ, ofRealVec (fun i => (a i : ℝ)) = ofIntVec a := fun a => by
      ext i; simp [ofRealVec, ofIntVec]
    simp only [Φ, h1]
  have hsurj : ∀ z, ∃ v, Φ v = z := by
    intro z
    have hz : z ∈ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨n, n', rfl⟩ := hx; exact ⟨_, hint n n'⟩
    | zero => exact ⟨(0 : ℝ) • 0, by rw [hsmul, zero_smul]⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact ⟨_, hadd v w⟩
    | smul r x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      exact ⟨_, hsmul r v⟩
  refine ⟨Φ '' Set.Icc 0 1, isCompact_Icc.image hΦ, fun z => ?_⟩
  obtain ⟨v, rfl⟩ := hsurj z
  refine ⟨_, ⟨(fun i => Int.fract (v.1 i), fun i => Int.fract (v.2 i)), ⟨⟨fun i => ?_, fun i => ?_⟩,
    fun i => ?_, fun i => ?_⟩, rfl⟩, fun i => ⌊v.1 i⌋, fun i => ⌊v.2 i⌋, ?_⟩
  · exact Int.fract_nonneg _
  · exact Int.fract_nonneg _
  · exact (Int.fract_lt_one _).le
  · exact (Int.fract_lt_one _).le
  · rw [← hint, sub_eq_iff_eq_add, ← hadd]
    congr 1
    ext i <;> simp

theorem isIntegral_and_rational_theta :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c
        i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
        : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) /
        2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
        : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g →
        ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z
        : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
        : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
        g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z z' : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g →
        ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → f z = γ * f z') → z - z' ∈ periodLattice τ) → (∀ (g : ℕ) (τ : Matrix (Fin
        g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ
        : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ
        ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n
        ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
        g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
        τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
        ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I
        : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z
        : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N
        : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸
        I) ≤ (g + 1 : ℕ)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
        g) → ∀ N : ℕ, 3 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t
        : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ)
        : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → ∀ p : (Fin g → Fin
        N) → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z
        : Fin g → ℂ), p = fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ)
        • τ)) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d
        : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d)
        ℂ)) (q : MvPolynomial (Fin
        d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial
        (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p,
        p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d)
        ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d)
        ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C
        : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d)
        ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map
        (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ
        z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d →
        ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval
        z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map
        (MvPolynomial.eval z.1)).eval z.2) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
        g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (d : ℕ) (f : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * f z) → IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g
        → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) •
        τ))) (fun p : ℂ × (Fin g → ℂ) => p.1 ^ d * f p.2) ∧ ∃ a ∈ (Algebra.adjoin ℂ (Set.range
        fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ)
        : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))), ∃ b ∈ (Algebra.adjoin ℂ (Set.range fun (c
        : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N
        : ℂ) • p.2) ((N : ℂ) • τ))), b ≠ 0 ∧ b * (fun p : ℂ × (Fin g →
        ℂ) => p.1 ^ d * f p.2) = a) := by
  intro hbas hspan hnz hsep htan hlat _ hcl hnoeth hrat g τ hτ N hN d f hf
  set u : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) with hu
  set θ : (Fin g → ℂ) → (Fin g → Fin N) → ℂ := fun z c => u c z with hθ
  have hb := (hbas g τ hτ N (by omega)).1
  have hud : ∀ c, Differentiable ℂ (u c) := fun c => (hb c).1
  have hθd : Differentiable ℂ θ := differentiable_pi.2 hud
  have hsp := hspan g τ hτ N (by omega)
  have hN0 : ∀ z, θ z ≠ 0 := by
    intro z h0
    obtain ⟨f, hf, hf0⟩ := hnz g τ hτ N (by omega) z
    apply hf0
    have h1 := hsp f hf
    clear hf0 hf
    induction h1 using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact congrFun h0 c
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hS : ∀ (z z' : Fin g → ℂ) (γ : ℂ), θ z = γ • θ z' →
      z - z' ∈ (periodLattice τ : Set (Fin g → ℂ)) := by
    intro z z' γ h0
    refine hsep g τ hτ N hN z z' γ fun f hf => ?_
    have h1 := hsp f hf
    clear hf
    induction h1 using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact congrFun h0 c
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy, mul_add]
    | smul r x _ hx => simp [hx, mul_left_comm]
  have hT : ∀ (z ξ : Fin g → ℂ) (γ : ℂ), fderiv ℂ θ z ξ = γ • θ z → ξ = 0 := by
    intro z ξ γ h0
    refine htan g τ hτ N hN z ξ γ fun f hf => ?_
    have h1 := hsp f hf
    clear hf
    suffices Differentiable ℂ f ∧ fderiv ℂ f z ξ = γ * f z from this.2
    induction h1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      refine ⟨hud c, ?_⟩
      rw [hθ, fderiv_pi fun c => hud c z] at h0
      exact congrFun h0 c
    | zero => exact ⟨differentiable_const 0, by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      rw [fderiv_add (hx.1 z) (hy.1 z)]
      simp [hx.2, hy.2, mul_add]
    | smul r x _ hx =>
      refine ⟨hx.1.const_smul r, ?_⟩
      rw [fderiv_const_smul (hx.1 z)]
      simp [hx.2, mul_left_comm]
  have hL : ∀ l ∈ (periodLattice τ : Set (Fin g → ℂ)), ∃ κ : (Fin g → ℂ) → ℂ, Continuous κ ∧
      ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧ f (z + l) = κ z ^ d * f z := by
    rintro _ ⟨n, n', rfl⟩
    refine ⟨fun z => eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)), ?_,
      fun z => ⟨Complex.exp_ne_zero _, funext fun c => ?_, ?_⟩⟩
    · unfold eC
      fun_prop
    · rw [← add_assoc]
      exact (hb c).2 n n' z
    · rw [← add_assoc, hf.2 n n' z]
      congr 1
      simp only [eC]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
  obtain ⟨K, hK, hP⟩ := exists_compact_reps τ (hlat g τ hτ).2.1
  obtain ⟨C, hC, hgr⟩ := growth hK hθd.continuous hf.1.continuous hN0 hP hL
  obtain ⟨c₀, hc₀⟩ := Function.ne_iff.1 (hN0 0)
  have hf1 := hf.1
  refine isIntegral_and_rational hnoeth hrat
    (u := fun c (p : ℂ × (Fin g → ℂ)) => p.1 * u c p.2) (h := fun p => p.1 ^ d * f p.2)
    (fun c => differentiable_fst.mul ((hud c).comp differentiable_snd)) (by fun_prop)
    (fun y hy => ?_) (c₀ := c₀) (fun h0 => hc₀ ?_)
    (exists_analytic_descent hK hθd hf.1 hN0 hP hL hS hT) hC hgr
  · obtain ⟨t, z, h1⟩ := hcl g τ hτ N hN
      (⨅ e : ℂ × (Fin g → ℂ), RingHom.ker (MvPolynomial.eval fun c => e.1 * u c e.2))
      (fun F => by simp only [Ideal.mem_iInf, RingHom.mem_ker, Prod.forall]; rfl) y
      (fun F hF => hy F (by simpa only [Ideal.mem_iInf, RingHom.mem_ker] using hF))
    exact ⟨(t, z), h1⟩
  · simpa using congrFun h0 (1, 0)

end GlobalTheory.ThetaRational

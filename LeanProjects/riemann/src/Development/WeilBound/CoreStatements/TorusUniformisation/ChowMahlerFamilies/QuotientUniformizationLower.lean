import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactSphere

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace PositivityTheory.Xgn.QuotientUniformizationLower

open scoped ComplexOrder

theorem core_gram {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {N : ℕ}
    (b : Fin N → V) (Γ : Matrix (Fin N) (Fin N) ℂ) (hΓ : ∀ i j, Γ i j = core.inner (b i) (b j)) :
    (LinearIndependent ℂ b → Γ.PosDef) ∧
      ∀ c : Fin N → ℂ, star c ⬝ᵥ (Γ *ᵥ c) = core.inner (∑ i, c i • b i) (∑ i, c i • b i) := by
  have hzl : ∀ y : V, core.inner 0 y = 0 := fun y => by
    have h := core.smul_left 0 y 0
    simpa using h
  have hsl : ∀ (s : Finset (Fin N)) (f : Fin N → V) (y : V),
      core.inner (∑ i ∈ s, f i) y = ∑ i ∈ s, core.inner (f i) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => simpa using hzl y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, ih]
  have hconj : ∀ x y : V, core.inner x y = starRingEnd ℂ (core.inner y x) := fun x y =>
    (core.conj_inner_symm x y).symm
  have hsr : ∀ (s : Finset (Fin N)) (f : Fin N → V) (x : V),
      core.inner x (∑ i ∈ s, f i) = ∑ i ∈ s, core.inner x (f i) := by
    intro s f x
    rw [hconj, hsl, map_sum]
    exact Finset.sum_congr rfl fun i _ => (hconj x (f i)).symm
  have hsmr : ∀ (x y : V) (r : ℂ), core.inner x (r • y) = r * core.inner x y := by
    intro x y r
    rw [hconj, core.smul_left, map_mul, ← hconj]
    simp
  have hid : ∀ c : Fin N → ℂ, star c ⬝ᵥ (Γ *ᵥ c) = core.inner (∑ i, c i • b i) (∑ i, c i • b i) := by
    intro c
    rw [hsl]
    simp only [dotProduct, mulVec, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [core.smul_left, hsr, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmr, hΓ, Complex.star_def]
    ring
  refine ⟨fun hli => ?_, hid⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun c hc => ?_⟩
  · rw [hΓ, hΓ]
    exact core.conj_inner_symm (b i) (b j)
  · rw [hid]
    set x := ∑ i, c i • b i with hxdef
    have hx : x ≠ 0 := by
      intro h0
      apply hc
      funext i
      exact Fintype.linearIndependent_iff.1 hli c h0 i
    have him : (core.inner x x).im = 0 := by
      have h := congrArg Complex.im (core.conj_inner_symm x x)
      simp at h
      linarith
    have hre : 0 < (core.inner x x).re := by
      have h1 := core.re_inner_nonneg x
      rcases h1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hx
        apply core.definite
        exact Complex.ext (by simpa using h.symm) (by simpa using him)
    rw [Complex.pos_iff]
    exact ⟨hre, him.symm⟩

private theorem norm_sq_add_norm_sq_sub_eq_complete_square {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ) (hD : ∀ i j, ‖D i j‖ ≤ ε)
    (hε : 0 ≤ ε) (c : Fin N → ℂ) : ‖star c ⬝ᵥ (D *ᵥ c)‖ ≤ N * N * ε * ‖c‖ ^ 2 := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  calc ‖∑ i, star (c i) * ∑ j, D i j * c j‖ ≤ ∑ i, ‖star (c i) * ∑ j, D i j * c j‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, ε * ‖c‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, norm_star]
        have h1 := norm_le_pi_norm c i
        have h2 := norm_le_pi_norm c j
        calc ‖c i‖ * (‖D i j‖ * ‖c j‖) ≤ ‖c‖ * (ε * ‖c‖) := by
              gcongr
              exact hD i j
          _ = ε * ‖c‖ ^ 2 := by ring
    _ = N * N * ε * ‖c‖ ^ 2 := by simp [Finset.sum_const]; ring

private theorem exists_pos_mul_norm_sq_le_re_quadratic {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ)
    (hpos : ∀ c : Fin N → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ δ > 0, ∀ c : Fin N → ℂ, δ * ‖c‖ ^ 2 ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by
  by_cases hN : N = 0
  · subst hN
    refine ⟨1, one_pos, fun c => ?_⟩
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    simp
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
  have hne : (sphere (0 : Fin N → ℂ) 1).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    rw [mem_sphere_zero_iff_norm, pi_norm_const]
    simp
  have hcont : Continuous fun c : Fin N → ℂ => (star c ⬝ᵥ (G *ᵥ c)).re := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    fun_prop
  obtain ⟨c0, hc0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℂ) 1).exists_isMinOn hne hcont.continuousOn
  have hc0n : ‖c0‖ = 1 := mem_sphere_zero_iff_norm.1 hc0
  have hc0z : c0 ≠ 0 := fun h => by rw [h, norm_zero] at hc0n; exact zero_ne_one hc0n
  refine ⟨(star c0 ⬝ᵥ (G *ᵥ c0)).re, hpos c0 hc0z, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp
  set t : ℝ := ‖c‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hc
  set c' : Fin N → ℂ := ((t⁻¹ : ℝ) : ℂ) • c with hc'_def
  have hc' : c' ∈ sphere (0 : Fin N → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hc'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos ht, inv_mul_cancel₀ ht.ne']
  have hcc : c = ((t : ℝ) : ℂ) • c' := by
    rw [hc'_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
  have hq : (star c ⬝ᵥ (G *ᵥ c)).re = t ^ 2 * (star c' ⬝ᵥ (G *ᵥ c')).re := by
    rw [hcc, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [← _root_.mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  have hm : (star c0 ⬝ᵥ (G *ᵥ c0)).re ≤ (star c' ⬝ᵥ (G *ᵥ c')).re := hmin hc'
  rw [hq, mul_comm]
  exact mul_le_mul_of_nonneg_left hm (sq_nonneg t)

theorem analytic {U : Type} [MetricSpace U] [ProperSpace U] (o : U) {N g : ℕ}
    (b : U → Fin N → Fin g → ℂ) (hb : ∀ i j, ContinuousOn (fun u => b u i j) (ball o 1))
    (Γ : U → Matrix (Fin N) (Fin N) ℂ) (hΓ : ∀ i j, ContinuousOn (fun u => Γ u i j) (ball o 1))
    (hc : ∀ u ∈ ball o 1, ∃ core : InnerProductSpace.Core ℂ (Fin g → ℂ),
      ∀ i j, Γ u i j = core.inner (b u i) (b u j))
    (h0 : LinearIndependent ℂ (b o) ∧ Submodule.span ℂ (Set.range (b o)) = ⊤) :
    ∃ ρ Kc : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < Kc ∧ ∀ u ∈ ball o ρ, ∀ core : InnerProductSpace.Core ℂ (Fin g → ℂ),
      (∀ i j, Γ u i j = core.inner (b u i) (b u j)) → ∀ x : Fin g → ℂ,
        ∑ i, ‖x i‖ ^ 2 ≤ Kc * (core.inner x x).re := by
  obtain ⟨core0, hcore0⟩ := hc o (mem_ball_self one_pos)
  have hpos0 : ∀ c : Fin N → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (Γ o *ᵥ c)).re := by
    intro c hc0
    have hpd := (core_gram core0 (b o) (Γ o) hcore0).1 h0.1
    exact (Complex.pos_iff.1 (hpd.dotProduct_mulVec_pos hc0)).1
  obtain ⟨δ, hδ, hδc⟩ := exists_pos_mul_norm_sq_le_re_quadratic (Γ o) hpos0
  have hNg : Module.finrank ℂ (Fin N → ℂ) = Module.finrank ℂ (Fin g → ℂ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    have hB := Module.finrank_eq_card_basis (Module.Basis.mk h0.1 h0.2.ge)
    simpa using hB.symm
  set Mb : ℝ := ∑ i, (‖b o i‖ + 1) with hMb_def
  have hMb : 0 ≤ Mb := Finset.sum_nonneg fun i _ => by positivity
  set ε : ℝ := δ / (2 * (N * N + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hmem : ball o 1 ∈ 𝓝 o := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hcont : ∀ᶠ u in 𝓝 o, (∀ i j, ‖Γ u i j - Γ o i j‖ < ε) ∧ (∀ i, ‖b u i‖ < ‖b o i‖ + 1) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      have hca := (hΓ i j).continuousAt hmem
      exact (hca.eventually (Metric.ball_mem_nhds (Γ o i j) hε)).mono fun u hu => by
        rwa [dist_eq_norm] at hu
    · rw [Filter.eventually_all]
      intro i
      have hcb : ContinuousAt (fun u => b u i) o :=
        continuousAt_pi.2 fun j => (hb i j).continuousAt hmem
      exact hcb.norm.eventually (gt_mem_nhds (lt_add_one ‖b o i‖))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hcont
  refine ⟨min r 1, (g * Mb ^ 2 + 1) * (2 / δ), lt_min hr one_pos, min_le_right _ _, by positivity, ?_⟩
  intro u hu core hcore x
  have hu' : u ∈ ball o r := ball_subset_ball (min_le_left _ _) hu
  obtain ⟨hΓu, hbu⟩ := hball u hu'
  have hid := (core_gram core (b u) (Γ u) hcore).2
  have h5 : (N : ℝ) * N * ε ≤ δ / 2 := by
    have hN : (0 : ℝ) ≤ N * N := by positivity
    have e1 : (N : ℝ) * N * ε = δ / 2 * ((N * N) / (N * N + 1)) := by
      rw [hε_def]; field_simp
    rw [e1]
    calc δ / 2 * ((N * N) / (N * N + 1)) ≤ δ / 2 * 1 := by
          gcongr
          exact (div_le_one (by positivity)).2 (by linarith)
      _ = δ / 2 := mul_one _
  have hlow : ∀ c : Fin N → ℂ, δ / 2 * ‖c‖ ^ 2 ≤ (star c ⬝ᵥ (Γ u *ᵥ c)).re := by
    intro c
    have h1 := hδc c
    have h2 := norm_sq_add_norm_sq_sub_eq_complete_square (Γ u - Γ o) ε (fun i j => (hΓu i j).le) hε.le c
    have h3 : star c ⬝ᵥ (Γ u *ᵥ c) = star c ⬝ᵥ (Γ o *ᵥ c) + star c ⬝ᵥ ((Γ u - Γ o) *ᵥ c) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      ring
    have h4 : |(star c ⬝ᵥ ((Γ u - Γ o) *ᵥ c)).re| ≤ N * N * ε * ‖c‖ ^ 2 :=
      (Complex.abs_re_le_norm _).trans h2
    have h6 := neg_abs_le (star c ⬝ᵥ ((Γ u - Γ o) *ᵥ c)).re
    have h7 := mul_le_mul_of_nonneg_right h5 (sq_nonneg ‖c‖)
    rw [h3, Complex.add_re]
    nlinarith
  have hz : core.inner (0 : Fin g → ℂ) 0 = 0 := by
    have h := core.smul_left 0 0 0
    simpa using h
  let B := Fintype.linearCombination ℂ (b u)
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc0
    by_contra hne
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hne
    have h1 := hlow c
    have hs : ∑ i, c i • b u i = 0 := by
      rw [Fintype.linearCombination_apply] at hc0
      exact hc0
    rw [hid c, hs, hz, Complex.zero_re] at h1
    have : 0 < δ / 2 * ‖c‖ ^ 2 := by positivity
    linarith
  obtain ⟨c, hcx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hNg).1 hinj x
  have hcx' : ∑ i, c i • b u i = x := by
    rw [Fintype.linearCombination_apply] at hcx
    exact hcx
  have hxc : ‖x‖ ≤ Mb * ‖c‖ := by
    rw [← hcx']
    calc ‖∑ i, c i • b u i‖ ≤ ∑ i, ‖c i • b u i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c‖ * (‖b o i‖ + 1) := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm c i) (hbu i).le (norm_nonneg _) (norm_nonneg _)
      _ = Mb * ‖c‖ := by rw [← Finset.mul_sum, hMb_def]; ring
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ g * ‖x‖ ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin g, ‖x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
      _ = g * ‖x‖ ^ 2 := by simp
  have hre := hlow c
  rw [hid c, hcx'] at hre
  have hg0 : (0 : ℝ) ≤ g := by positivity
  calc ∑ i, ‖x i‖ ^ 2 ≤ g * ‖x‖ ^ 2 := hsum
    _ ≤ g * (Mb * ‖c‖) ^ 2 := by gcongr
    _ ≤ (g * Mb ^ 2 + 1) * ‖c‖ ^ 2 := by nlinarith [sq_nonneg ‖c‖]
    _ = (g * Mb ^ 2 + 1) * (2 / δ) * (δ / 2 * ‖c‖ ^ 2) := by field_simp
    _ ≤ (g * Mb ^ 2 + 1) * (2 / δ) * (core.inner x x).re := by gcongr

end PositivityTheory.Xgn.QuotientUniformizationLower

theorem PositivityTheory.Xgn.quotient_uniformization_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re := by
  intro E _ _ _ H D l Xo σ n a C X t jj m Ω _ ξ K J y Li _ _ M h N s sc ww hww hMz hco hval hbasis
  classical
  have hcart : IsGrpPullback C.t.G t.G jj m.φ := m.cart
  have hpull : ∀ (u : Fin n → ℂ) (Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ)),
      ∃ M' : LieModel t.G (spMap (C.ψ u) ≫ jj) (Fin C.g → ℂ),
        ∀ e, (Mz.pt e).left ≫ m.φ = (M'.pt e).left := fun u Mz =>
    (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ jj m.φ hcart ℂ (spMap (C.ψ u)) (Fin C.g → ℂ)).2 Mz
  let b : (Fin n → ℂ) → Fin N → Fin C.g → ℂ := fun u i k => C.ψ u (sc i k)
  let vv : ∀ u, u ∈ ball (0 : Fin n → ℂ) 1 → Fin N → (epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G) :=
    fun u hu i => Classical.choose (hval u hu i)
  have hvv : ∀ u hu i, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) (vv u hu i) ∧
      (vv u hu i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ :=
    fun u hu i => Classical.choose_spec (hval u hu i)
  let Γ : (Fin n → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun u i j =>
    if hu : u ∈ ball (0 : Fin n → ℂ) 1 then h.ip _ (vv u hu i) (vv u hu j) else 0
  have hkey : ∀ u (hu : u ∈ ball (0 : Fin n → ℂ) 1)
      (Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ)),
      (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) →
      ∀ M' : LieModel t.G (spMap (C.ψ u) ≫ jj) (Fin C.g → ℂ),
      (∀ e, (Mz.pt e).left ≫ m.φ = (M'.pt e).left) → ∀ i, M'.pt (b u i) = vv u hu i := by
    intro u hu Mz hl M' hM' i
    apply Over.OverMorphism.ext
    rw [← hM', (hvv u hu i).2]
    have hli := hl (sc i)
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts at hli
    rw [Category.comp_id] at hli
    show (Mz.pt (fun k => C.ψ u (sc i k))).left ≫ m.φ = _
    rw [hli, Category.assoc]
  have hcore : ∀ u (hu : u ∈ ball (0 : Fin n → ℂ) 1)
      (Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ)),
      (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) →
      ∃ core : InnerProductSpace.Core ℂ (Fin C.g → ℂ),
        (∀ i j, Γ u i j = core.inner (b u i) (b u j)) ∧
        ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G),
          (Mz.pt x).left ≫ m.φ = v₀.left → h.ip _ v₀ v₀ = core.inner x x := by
    intro u hu Mz hl
    obtain ⟨M', hM'⟩ := hpull u Mz
    obtain ⟨core, hcoreip⟩ := h.herm _ (Fin C.g → ℂ) M'
    refine ⟨core, fun i j => ?_, fun x v₀ hx => ?_⟩
    · simp only [Γ, dif_pos hu]
      rw [hcoreip, hkey u hu Mz hl M' hM' i, hkey u hu Mz hl M' hM' j]
    · have hpt : M'.pt x = v₀ := Over.OverMorphism.ext (by rw [← hM']; exact hx)
      rw [hcoreip, hpt]
  have hΓc : ∀ i j, ContinuousOn (fun u => Γ u i j) (ball 0 1) := by
    intro i j
    obtain ⟨F, hF, hFeq⟩ := h.cont (s i) (s j)
    have heq : ∀ u ∈ ball (0 : Fin n → ℂ) 1, F (ww u) = Γ u i j := by
      intro u hu
      simp only [Γ, dif_pos hu]
      exact hFeq _ (ww u) _ _ (hco u hu) (hvv u hu i).1 (hvv u hu j).1
    refine ContinuousOn.congr (hF.comp hww ?_) (fun u hu => (heq u hu).symm)
    intro u hu
    exact ⟨_, vv u hu i, vv u hu j, hco u hu, (hvv u hu i).1, (hvv u hu j).1⟩
  have hbc : ∀ i k, ContinuousOn (fun u => b u i k) (ball 0 1) := fun i k =>
    (C.hol.2 (sc i k)).continuousOn
  have h01 : (0 : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) 1 := mem_ball_self one_pos
  obtain ⟨Mz0, hMz0⟩ := hMz 0 h01
  obtain ⟨M0', hM0'⟩ := hpull 0 Mz0
  have h0 : LinearIndependent ℂ (b 0) ∧ Submodule.span ℂ (Set.range (b 0)) = ⊤ :=
    hbasis (Fin C.g → ℂ) M0' (b 0) (fun i => by
      rw [hkey 0 h01 Mz0 hMz0 M0' hM0' i]
      exact (hvv 0 h01 i).1)
  obtain ⟨ρ, Kc, hρ, hρ1, hKc, hbound⟩ :=
    PositivityTheory.Xgn.QuotientUniformizationLower.analytic (0 : Fin n → ℂ) b hbc Γ hΓc
      (fun u hu => by
        obtain ⟨Mz, hl⟩ := hMz u hu
        obtain ⟨core, hc1, -⟩ := hcore u hu Mz hl
        exact ⟨core, hc1⟩) h0
  refine ⟨ρ, Kc, hρ, hKc, fun u hu Mz hl x v₀ hx => ?_⟩
  have hu1 : u ∈ ball (0 : Fin n → ℂ) 1 := ball_subset_ball hρ1 hu
  obtain ⟨core, hc1, hc2⟩ := hcore u hu1 Mz hl
  rw [hc2 x v₀ hx]
  exact hbound u hu core hc1 x

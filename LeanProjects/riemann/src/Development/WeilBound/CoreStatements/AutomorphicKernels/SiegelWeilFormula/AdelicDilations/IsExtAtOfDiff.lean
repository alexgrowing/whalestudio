import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected

noncomputable section

open Filter Topology GlobalTheory.Cont

namespace PositivityTheory.SiegelWeilFormula.AStep

theorem iterDerivPow (k : ℕ) : ∀ (f g : ℂ → ℂ) (s₀ : ℂ), AnalyticAt ℂ g s₀ → (f =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * g z) →
    (∀ i < k, iteratedDeriv i f s₀ = 0) ∧ iteratedDeriv k f s₀ = (k.factorial : ℂ) * g s₀ := by
  induction k with
  | zero =>
    intro f g s₀ _ hf
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    simp [iteratedDeriv_zero, hf.self_of_nhds]
  | succ k ih =>
    intro f g s₀ hg hf
    set h : ℂ → ℂ := fun z => ((k : ℂ) + 1) * g z + (z - s₀) * deriv g z with hh
    have hha : AnalyticAt ℂ h s₀ := by
      have := hg.deriv
      simp only [hh]; fun_prop
    have hdf : deriv f =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * h z := by
      refine hf.deriv.trans ?_
      filter_upwards [hg.eventually_analyticAt] with z hz
      have hd : HasDerivAt (fun z => (z - s₀) ^ (k + 1) * g z)
          (((k + 1 : ℕ) : ℂ) * (z - s₀) ^ k * 1 * g z + (z - s₀) ^ (k + 1) * deriv g z) z :=
        (((hasDerivAt_id z).sub_const s₀).pow (k + 1)).mul hz.differentiableAt.hasDerivAt
      rw [hd.deriv, hh]; push_cast; ring
    obtain ⟨ih1, ih2⟩ := ih (deriv f) h s₀ hha hdf
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · simp [iteratedDeriv_zero, hf.self_of_nhds]
      · rw [iteratedDeriv_succ']; exact ih1 i (by omega)
    · rw [iteratedDeriv_succ', ih2, hh, Nat.factorial_succ]; push_cast; simp; ring

theorem polyFac (p : Polynomial ℂ) (s₀ : ℂ) :
    ∃ q : Polynomial ℂ, (∀ z, p.eval z = (z - s₀) ^ p.rootMultiplicity s₀ * q.eval z) ∧ (p ≠ 0 → q.eval s₀ ≠ 0) := by
  refine ⟨p /ₘ (Polynomial.X - Polynomial.C s₀) ^ p.rootMultiplicity s₀, fun z => ?_,
    fun hp => Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero s₀ hp⟩
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq s₀]
  simp

theorem eqNhds {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝[≠] x] g) (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f =ᶠ[𝓝 x] g := by
  have hx : f x = g x :=
    tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds) ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)
  filter_upwards [eventually_nhdsWithin_iff.mp h] with z hz
  by_cases e : z = x
  · subst e; exact hx
  · exact hz e

theorem isExtAt_of_diff {U : Set ℂ} {e φ : ℂ → ℂ} {t : ℝ} {s₀ : ℂ} (hU : IsOpen U) (hR : IsRightDomain U) (hs : s₀ ∈ U)
    (he : DifferentiableOn ℂ e U) (heq : ∀ z : ℂ, t < z.re → e z = φ z) : IsExtAt φ s₀ e :=
  ⟨U, hs, hR, fun z hz => ((he.analyticOnNhd hU) z hz).meromorphicAt, t, fun z hz => heq z hz⟩

theorem isExtAt_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (s₀ : ℂ) : IsExtAt f s₀ f :=
  (isMerExt_self isRightDomain_univ fun z _ => (hf.analyticAt z).meromorphicAt).isExtAt trivial

theorem pderiv_lt (p : Polynomial ℂ) (s₀ : ℂ) (j : ℕ) (hj : j < p.rootMultiplicity s₀) :
    iteratedDeriv j (fun z => p.eval z) s₀ = 0 := by
  obtain ⟨q, hq, -⟩ := polyFac p s₀
  exact (iterDerivPow _ _ (fun z => q.eval z) s₀ (q.differentiable.analyticAt s₀)
    (Eventually.of_forall hq)).1 j hj

theorem ordVal (U : Set ℂ) (p : Polynomial ℂ) (e h : ℂ → ℂ) (t : ℝ) (s₀ c : ℂ) (hU : IsOpen U) (hR : IsRightDomain U)
    (hs : s₀ ∈ U) (hp : p ≠ 0) (he : DifferentiableOn ℂ e U) (heq : ∀ z : ℂ, t < z.re → e z = p.eval z * h z)
    (hv : HolValueAt h s₀ c) : ∀ j ≤ p.rootMultiplicity s₀, iteratedDeriv j e s₀ = iteratedDeriv j (fun z => p.eval z) s₀ * c := by
  obtain ⟨H, hH, hHa, hHc⟩ := hv
  obtain ⟨q, hq, -⟩ := polyFac p s₀
  set k := p.rootMultiplicity s₀
  have hE : IsExtAt (fun z => p.eval z * h z) s₀ e := isExtAt_of_diff hU hR hs he heq
  have hP : IsExtAt (fun z => p.eval z * h z) s₀ (fun z => p.eval z * H z) := (isExtAt_entire p.differentiable s₀).mul hH
  have hea : AnalyticAt ℂ e s₀ := (he.analyticOnNhd hU) s₀ hs
  have hPa : AnalyticAt ℂ (fun z => p.eval z * H z) s₀ := (p.differentiable.analyticAt s₀).mul hHa
  have h1 : e =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * (q.eval z * H z) := by
    refine (eqNhds (hE.eventuallyEq hP) hea.continuousAt hPa.continuousAt).trans (Eventually.of_forall fun z => ?_)
    simp only [hq z]; ring
  have A := iterDerivPow k e _ s₀ ((q.differentiable.analyticAt s₀).mul hHa) h1
  have B := iterDerivPow k _ (fun z => q.eval z) s₀ (q.differentiable.analyticAt s₀) (Eventually.of_forall hq)
  intro j hj
  rcases hj.lt_or_eq with hj | hj
  · rw [A.1 j hj, B.1 j hj, zero_mul]
  · subst hj; rw [A.2, B.2, Pi.mul_apply, hHc]; ring

theorem wrap (U : Set ℂ) (p : Polynomial ℂ) (e h : ℂ → ℂ) (t : ℝ) (s₀ c : ℂ) (hU : IsOpen U) (hR : IsRightDomain U)
    (hs : s₀ ∈ U) (hp : p ≠ 0) (he : DifferentiableOn ℂ e U) (heq : ∀ z : ℂ, t < z.re → e z = p.eval z * h z)
    (hlow : ∀ j < p.rootMultiplicity s₀, iteratedDeriv j e s₀ = 0)
    (htop : iteratedDeriv (p.rootMultiplicity s₀) e s₀ =
      iteratedDeriv (p.rootMultiplicity s₀) (fun z => p.eval z) s₀ * c) : HolValueAt h s₀ c := by
  obtain ⟨q, hq, hq0⟩ := polyFac p s₀
  have hq0 := hq0 hp
  set k := p.rootMultiplicity s₀
  have hea : AnalyticAt ℂ e s₀ := (he.analyticOnNhd hU) s₀ hs
  obtain ⟨g, hg, hge⟩ := (natCast_le_analyticOrderAt hea).1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hea).2 hlow)
  have hge' : e =ᶠ[𝓝 s₀] fun z => (z - s₀) ^ k * g z := hge.mono fun z hz => by rw [hz, smul_eq_mul]
  have A := (iterDerivPow k e g s₀ hg hge').2
  have B := (iterDerivPow k _ (fun z => q.eval z) s₀ (q.differentiable.analyticAt s₀) (Eventually.of_forall hq)).2
  have hgc : g s₀ = q.eval s₀ * c := by
    rw [A, B] at htop
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    apply mul_left_cancel₀ hf; rw [htop]; ring

  have hE : IsExtAt (fun z => p.eval z * h z) s₀ e := isExtAt_of_diff hU hR hs he heq
  have hD : IsExtAt (fun z => p.eval z * h z / p.eval z) s₀ (fun z => e z / p.eval z) :=
    hE.div (isExtAt_entire p.differentiable s₀)
  obtain ⟨σ, hσ⟩ := ((Polynomial.finite_setOfPred_isRoot hp).image Complex.re).bddAbove
  have hR' : EqRight (fun z => p.eval z * h z / p.eval z) h := by
    refine ⟨σ, fun z hz => ?_⟩
    have hpz : p.eval z ≠ 0 := fun h0 => by
      have := hσ ⟨z, h0, rfl⟩
      exact absurd (mem_rightOf.1 hz) (not_lt.2 this)
    exact mul_div_cancel_left₀ (h z) hpz
  refine (hD.congr hR').holValueAt_iff.2 ?_
  have hlim : Tendsto (fun z => g z / q.eval z) (𝓝[≠] s₀) (𝓝 c) := by
    have : ContinuousAt (fun z => g z / q.eval z) s₀ :=
      hg.continuousAt.div (q.differentiable.analyticAt s₀).continuousAt hq0
    have hv : g s₀ / q.eval s₀ = c := by rw [hgc]; field_simp
    rw [← hv]; exact this.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hge', self_mem_nhdsWithin] with z hz hz'
  have hne : (z - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz')
  rw [hz, hq z, mul_div_mul_left _ _ hne]

theorem valLaw (h h' : ℂ → ℂ) (t : ℝ) (α β s₀ v v' : ℂ) (hl : ∀ z : ℂ, t < z.re → h' z = Complex.exp (α + β * z) * h z)
    (hv : HolValueAt h s₀ v) (hv' : HolValueAt h' s₀ v') : v' = Complex.exp (α + β * s₀) * v := by
  have hx : Differentiable ℂ fun z => Complex.exp (α + β * z) := by fun_prop
  have h1 : HolValueAt (fun z => Complex.exp (α + β * z)) s₀ (Complex.exp (α + β * s₀)) :=
    ⟨_, isExtAt_entire hx s₀, hx.analyticAt s₀, rfl⟩
  have h2 := (h1.mul hv).congr ⟨t, fun z hz => (hl z hz).symm⟩
  exact hv'.unique h2

theorem lawSep (U : Set ℂ) (p : Polynomial ℂ) (t : ℝ) (s₀ : ℂ) (j : ℕ) (a a' c₁ c₁' c₂ c₂' : ℂ → ℂ) (v v' α β : ℂ)
    (hU : IsOpen U) (hR : IsRightDomain U) (hs : s₀ ∈ U) (hp : p ≠ 0) (hj : j ≤ p.rootMultiplicity s₀)
    (ha : DifferentiableOn ℂ a U) (ha' : DifferentiableOn ℂ a' U)
    (hlo : ∀ i < j, iteratedDeriv i a s₀ = 0) (hlo' : ∀ i < j, iteratedDeriv i a' s₀ = 0)
    (he : ∀ z : ℂ, t < z.re → a z = p.eval z * (c₁ z + c₂ z)) (he' : ∀ z : ℂ, t < z.re → a' z = p.eval z * (c₁' z + c₂' z))
    (hv : HolValueAt c₁ s₀ v) (hv' : HolValueAt c₁' s₀ v')
    (hl : ∀ z : ℂ, t < z.re → c₂' z = Complex.exp (α + β * z) * c₂ z) :
    iteratedDeriv j a' s₀ - iteratedDeriv j (fun z => p.eval z) s₀ * v' =
      Complex.exp (α + β * s₀) * (iteratedDeriv j a s₀ - iteratedDeriv j (fun z => p.eval z) s₀ * v) := by
  obtain ⟨C, hC, hCa, hCv⟩ := hv
  obtain ⟨C', hC', hCa', hCv'⟩ := hv'
  obtain ⟨q, hq, -⟩ := polyFac p s₀
  set k := p.rootMultiplicity s₀
  set E : ℂ → ℂ := fun z => Complex.exp (α + β * z) with hEdef
  have hEd : Differentiable ℂ E := by simp only [hEdef]; fun_prop

  set gp : ℂ → ℂ := fun z => (z - s₀) ^ (k - j) * q.eval z with hgp
  have hgpa : AnalyticAt ℂ gp s₀ := by
    have := q.differentiable.analyticAt s₀
    simp only [hgp]; fun_prop
  have hpj : ∀ z, p.eval z = (z - s₀) ^ j * gp z := fun z => by
    rw [hq z, hgp]; simp only; rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
  have hP := (iterDerivPow j _ gp s₀ hgpa (Eventually.of_forall hpj)).2

  have haa : AnalyticAt ℂ a s₀ := (ha.analyticOnNhd hU) s₀ hs
  have haa' : AnalyticAt ℂ a' s₀ := (ha'.analyticOnNhd hU) s₀ hs
  obtain ⟨ga, hga, hgae⟩ := (natCast_le_analyticOrderAt haa).1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero haa).2 hlo)
  obtain ⟨ga', hga', hgae'⟩ :=
    (natCast_le_analyticOrderAt haa').1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero haa').2 hlo')
  simp only [smul_eq_mul] at hgae hgae'
  have hA := (iterDerivPow j a ga s₀ hga hgae).2
  have hA' := (iterDerivPow j a' ga' s₀ hga' hgae').2

  have hX : IsExtAt (fun z => p.eval z * (c₁ z + c₂ z) - p.eval z * c₁ z) s₀ (fun z => a z - p.eval z * C z) :=
    (isExtAt_of_diff hU hR hs ha he).map₂ (· - ·) (fun _ => .fun_sub) ((isExtAt_entire p.differentiable s₀).mul hC)
  have hX' : IsExtAt (fun z => p.eval z * (c₁' z + c₂' z) - p.eval z * c₁' z) s₀ (fun z => a' z - p.eval z * C' z) :=
    (isExtAt_of_diff hU hR hs ha' he').map₂ (· - ·) (fun _ => .fun_sub) ((isExtAt_entire p.differentiable s₀).mul hC')
  have hY : IsExtAt (fun z => E z * (p.eval z * (c₁ z + c₂ z) - p.eval z * c₁ z)) s₀
      (fun z => E z * (a z - p.eval z * C z)) := (isExtAt_entire hEd s₀).mul hX
  have hY' : IsExtAt (fun z => p.eval z * (c₁' z + c₂' z) - p.eval z * c₁' z) s₀ (fun z => E z * (a z - p.eval z * C z)) :=
    hY.congr ⟨t, fun z hz => by simp only [hEdef]; rw [hl z hz]; ring⟩
  have hev := hX'.eventuallyEq hY'

  set Φ : ℂ → ℂ := fun z => ga z - gp z * C z with hΦ
  set Φ' : ℂ → ℂ := fun z => ga' z - gp z * C' z with hΦ'
  have hΦa : AnalyticAt ℂ (fun z => E z * Φ z) s₀ := by
    have := hEd.analyticAt s₀
    simp only [hΦ]; fun_prop
  have hΦa' : AnalyticAt ℂ Φ' s₀ := by simp only [hΦ']; fun_prop
  have hlim : Φ' =ᶠ[𝓝[≠] s₀] fun z => E z * Φ z := by
    filter_upwards [hev, nhdsWithin_le_nhds hgae, nhdsWithin_le_nhds hgae', self_mem_nhdsWithin] with z h1 h2 h3 hz
    have hne : (z - s₀) ^ j ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
    apply mul_left_cancel₀ hne
    have := h1; simp only [h2, h3, hpj z] at this
    simp only [hΦ, hΦ']; linear_combination this
  have hval : Φ' s₀ = E s₀ * Φ s₀ := (eqNhds hlim hΦa'.continuousAt hΦa.continuousAt).self_of_nhds
  simp only [hΦ, hΦ', hEdef, hCv, hCv'] at hval
  rw [hA, hA', hP]; linear_combination (j.factorial : ℂ) * hval

end PositivityTheory.SiegelWeilFormula.AStep

end

import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {v : H} (hv : v ∈ W) : prj W v = v := by
  unfold prj
  exact Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure hv)

private theorem fixF_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    {U U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (h : U' ≤ U) : fixF μ U ≤ fixF μ U' := by
  unfold fixF
  exact biInf_mono fun u hu => h hu

private theorem eig_fix {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : v ∈ V ∧ 𝔞.A v = (x : ℂ) • v ∧ v ∈ fixF μ 𝔞.U := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  have h3 : 𝔞.A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 h2
  refine ⟨h1, h3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h4 := hA v
  rw [h3] at h4
  exact (Submodule.smul_mem_iff _ hx').1 h4

private theorem poly_ind {H σ ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ev : MvPolynomial σ (MvPolynomial ι ℂ) →+* (H →L[ℂ] H)) (f : MvPolynomial σ (MvPolynomial ι ℂ) →+* ℂ)
    (v : H) (s : Set σ) (h0 : ∀ c : ℂ, ev (C (C c)) v = f (C (C c)) • v)
    (h1 : ∀ i, ev (C (X i)) v = f (C (X i)) • v) (h2 : ∀ y ∈ s, ev (X y) v = f (X y) • v)
    (P : MvPolynomial σ (MvPolynomial ι ℂ)) (hP : ∀ y ∈ P.vars, y ∈ s) : ev P v = f P • v := by
  have hadd : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P + Q) v = f (P + Q) • v := by
    intro P Q hP hQ
    rw [map_add, map_add, ContinuousLinearMap.add_apply, hP, hQ, add_smul]
  have hmul : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P * Q) v = f (P * Q) • v := by
    intro P Q hP hQ
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hQ, map_smul, hP, smul_smul, mul_comm]
  have hC : ∀ c : MvPolynomial ι ℂ, ev (C c) v = f (C c) • v := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [C_add]; exact hadd _ _ hp hq
    | mul_X p i hp => rw [C_mul]; exact hmul _ _ hp (h1 i)
  have hm : P ∈ supported (MvPolynomial ι ℂ) s := mem_supported.2 fun y hy => hP y hy
  clear hP
  rw [supported_eq_adjoin_X] at hm
  induction hm using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact h2 y hy
  | algebraMap r => exact hC r
  | add p q _ _ hp hq => exact hadd _ _ hp hq
  | mul p q _ _ hp hq => exact hmul _ _ hp hq

private theorem eig_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) {w : Pl K} (hw : w ∉ 𝔞.S) :
    v ∈ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := by
  obtain ⟨h1, -, h2⟩ := eig_fix 𝔞 hA hx hv
  rw [Submodule.mem_inf, fixL]
  exact ⟨h1, fixF_anti μ (𝔞.max w hw) h2⟩

private theorem val_CC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (c : ℂ) : val (n := n) x Λ t (C (C c)) = c := by simp [val]

private theorem val_none {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) : val (n := n) x Λ t (C (X none)) = x := by simp [val]

private theorem val_some {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (y : Ix K n) :
    val (n := n) x Λ t (C (X (some y))) = x * (Λ y.1).esymm (y.2 + 1) := by simp [val]

private theorem val_X {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (w : Pl K) (i : Fin n) :
    val (n := n) x Λ t (X (w, i)) = (t w).esymm (i + 1) := by simp [val, hval]

private theorem ev_val {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x)
    {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev) {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (h : At μ 𝔞.S V Λ t) (P : PR K n) (hPv : ∀ y ∈ P.vars, y.1 ∉ 𝔞.S) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : ev P v = val x Λ t P • v := by
  obtain ⟨hvV, hAv, hvU⟩ := eig_fix 𝔞 hA hx hv
  obtain ⟨hI, hS⟩ := h
  have hO : Oinf μ 𝔞.ν 𝔞.a₀ v = (x : ℂ) • v := by
    rw [← hAv, Amp.A, ContinuousLinearMap.comp_apply, prj_self _ hvU]
  refine poly_ind ev (val x Λ t) v {y | y.1 ∉ 𝔞.S} (fun c => ?_) (fun o => ?_) (fun y hy => ?_) P hPv
  · rw [hev.const, val_CC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  · cases o with
    | none => rw [hev.amp, hAv, val_none]
    | some y =>
      obtain ⟨-, h1⟩ := hI y.1
      rw [hev.cen, Amp.Z, ContinuousLinearMap.comp_apply, prj_self _ hvU,
        h1 𝔞.ν 𝔞.a₀ 𝔞.smooth y.2 v hvV, hO, smul_smul, mul_comm, val_some]
  · obtain ⟨w, i⟩ := y
    obtain ⟨-, -, h1⟩ := hS w hy
    rw [hev.hecke w hy i, h1 i v (eig_fixL 𝔞 hA hx hv hy), val_X]

theorem UpperTheory.ConvolutionTheory.Ci.evVal :
    EvEx → ParEx → EvVal := by
  intro hE hP K _ _ _ n hn μ _ 𝔞 V x hx hV
  obtain ⟨-, -, hA, -⟩ := hE K n hn μ 𝔞
  obtain ⟨p1, p2, -⟩ := hP K n hn μ V hV
  refine ⟨fun hne => ?_, fun Λ t Λ' t' h h' => ?_, fun ev hev Λ t h P hPv v hv => ev_val 𝔞 hA hx hev h P hPv hv⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hB : ∀ w, ∃ B, w ∉ 𝔞.S → SSat μ V w B := by
      intro w
      by_cases hw : w ∈ 𝔞.S
      · exact ⟨0, fun h => absurd hw h⟩
      · obtain ⟨B, hB⟩ := (p2 w ((Submodule.ne_bot_iff _).2 ⟨v, eig_fixL 𝔞 hA hx hv hw, hv0⟩)).exists
        exact ⟨B, fun _ => hB⟩
    choose t ht using hB
    choose Λ hΛ using fun τ => (p1 τ).exists
    exact ⟨Λ, t, And.intro hΛ ht⟩
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', h2'⟩ := h'
    refine ⟨funext fun τ => ?_, fun w hw => ?_⟩
    · obtain ⟨m, -, hm⟩ := p1 τ
      beta_reduce at hm
      rw [hm (Λ τ) (h1 τ), hm (Λ' τ) (h1' τ)]
    · have h3 := h2 w hw
      obtain ⟨-, h4, -⟩ := h2 w hw
      obtain ⟨m, -, hm⟩ := p2 w h4
      beta_reduce at hm
      rw [hm (t w) h3, hm (t' w) (h2' w hw)]

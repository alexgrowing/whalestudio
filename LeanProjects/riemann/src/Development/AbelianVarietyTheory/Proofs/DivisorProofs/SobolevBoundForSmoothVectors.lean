import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivativesStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobolevGrowth

theorem lintegral_le_of_count {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {A : Set G} (hA : MeasurableSet A) {h : G → ℝ≥0∞} (hm : Measurable h) (hinv : ∀ γ ∈ Γ, ∀ g, h (γ * g) = h g)
    (M : ℝ) (hM : ∀ y, {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard : ℕ) : ℝ) ≤ M) :
    ∫⁻ x in A, h x ∂μ ≤ ENNReal.ofReal M * ∫⁻ x in 𝓕, h x ∂μ := by
  classical
  rw [← lintegral_indicator hA, h𝓕.lintegral_eq_tsum'' (A.indicator h), ← lintegral_tsum, ← lintegral_const_mul _ hm]
  · refine lintegral_mono fun y => ?_
    obtain ⟨hfin, hle⟩ := hM y
    have hfin' : {γ : Γ | (γ : G) * y ∈ A}.Finite := by
      refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    have hcard : hfin'.toFinset.card = {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard := by
      rw [← Set.ncard_eq_toFinset_card _ hfin', ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext g
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ.2, hγ⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨g, h1⟩, h2, rfl⟩
    rw [tsum_eq_sum (s := hfin'.toFinset)]
    · have : ∀ γ ∈ hfin'.toFinset, A.indicator h (γ • y) = h y := by
        intro γ hγ
        have h1 : (γ : G) * y ∈ A := by simpa using hγ
        change A.indicator h ((γ : G) * y) = h y
        rw [Set.indicator_of_mem h1, hinv _ γ.2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hle
    · intro γ hγ
      have h1 : (γ : G) * y ∉ A := by simpa using hγ
      change A.indicator h ((γ : G) * y) = 0
      exact Set.indicator_of_notMem h1 _
  · intro γ
    exact ((hm.indicator hA).comp (measurable_const_mul (γ : G))).aemeasurable

theorem lintegral_enorm_sq {Q : Type} [MeasurableSpace Q] (ν : Measure Q) (F : Lp ℂ 2 ν) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖F‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := ν) (p := 2) (by norm_num)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem sum_sq_le {α : Type} (S : List α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (S.map fun a => f a ^ 2).sum ≤ (S.map f).sum ^ 2 := by
  induction S with
  | nil => simp
  | cons a S ih =>
    have : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
    simp only [List.map_cons, List.sum_cons]
    nlinarith [hf a, mul_nonneg (hf a) this]

theorem integral_le_of_count {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Q] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (π : G → Q) (hmk : Measurable π)
    (hπ : ∀ γ ∈ Γ, ∀ g, π (γ * g) = π g) {Ω : Set G} (hΩ : IsCompact Ω) (z : G) (M : ℝ)
    (hM : ∀ y, {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 ((μ.restrict 𝓕).map π)) (φ : G → ℂ) (hφ : Continuous φ) (hr : ∀ᵐ x ∂μ, F (π x) = φ x) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  have hFm : Measurable fun x => ‖F x‖ₑ ^ 2 := (Lp.stronglyMeasurable F).measurable.enorm.pow_const 2
  have hA : IsCompact ((fun o => z * o) '' Ω) := hΩ.image (continuous_const_mul z)
  have key := lintegral_le_of_count μ Γ h𝓕 hA.measurableSet (hFm.comp hmk)
    (fun γ hγ g => by simp only [Function.comp, hπ γ hγ g]) (M ^ 2) (fun y => by
      have e : {γ : G | γ ∈ Γ ∧ γ * y ∈ (fun o => z * o) '' Ω} = {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o} :=
        Set.ext fun γ => and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => eq_comm
      rw [e]
      refine ⟨(hM y).1, ?_⟩
      have h1 := (hM y).2
      generalize Set.ncard _ = n at h1
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) n
      exact h2.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2))
  have e1 : ∫⁻ x in 𝓕, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← lintegral_enorm_sq]
    exact (lintegral_map hFm hmk).symm
  have e2 : ∫⁻ x in (fun o => z * o) '' Ω, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ =
      ∫⁻ x in Ω, ‖φ (z * x)‖ₑ ^ 2 ∂μ := by
    rw [((measurePreserving_mul_left μ z).setLIntegral_comp_emb (measurableEmbedding_mulLeft z)
      (fun x => ‖φ x‖ₑ ^ 2) Ω)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hr] with x hx
    simp only [Function.comp, hx]
  rw [e1, e2, ← ENNReal.ofReal_mul (sq_nonneg _)] at key
  have hc : Continuous fun x => ‖φ (z * x)‖ ^ 2 := (hφ.comp (continuous_const_mul z)).norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hc.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_of_eq_of_le ?_ key)
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem le_of_sums {α : Type} (S : List α) (I f : α → ℝ) (a C₁ C₂ n : ℝ) (N : ℕ) (hn : 0 ≤ n)
    (hI : ∀ l, 0 ≤ I l) (hf : ∀ l, 0 ≤ f l) (h1 : a ^ 2 ≤ C₁ * (S.map I).sum)
    (h2 : ∀ l ∈ S, I l ≤ (C₂ * n ^ N) ^ 2 * f l ^ 2) : a ≤ √|C₁| * |C₂| * n ^ N * (S.map f).sum := by
  have h2' : (S.map I).sum ≤ (S.map fun l => (C₂ * n ^ N) ^ 2 * f l ^ 2).sum := List.sum_le_sum h2
  rw [List.sum_map_mul_left] at h2'
  have h3 := sum_sq_le S f hf
  have h0 : 0 ≤ (S.map I).sum := List.sum_nonneg (by simpa using fun a _ => hI a)
  have hT : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
  refine le_of_sq_le_sq ?_ (by positivity)
  have e : (√|C₁| * |C₂| * n ^ N * (S.map f).sum) ^ 2 = |C₁| * ((C₂ * n ^ N) ^ 2 * (S.map f).sum ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    ring
  rw [e]
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans ?_)
  exact mul_le_mul_of_nonneg_left (h2'.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) (abs_nonneg _)

variable {D : D7}

theorem integral_le_adelic (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hp : FinPair V μ 𝓕)
    {Ω : Set (GA D V)} (hΩ : IsCompact Ω) (z : GA D V) (M : ℝ)
    (hM : ∀ y, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 (nuQ V μ 𝓕)) (φ : GA D V → ℂ) (hφ : Continuous φ) (hr : Repr V μ 𝓕 F φ) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  obtain ⟨-, -, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := hp.haar
  exact integral_le_of_count μ (GQ V) hp.fd (autMk V) measurable_quotient_mk''
    (fun γ hγ g => Quotient.sound (QuotientGroup.rightRel_apply.2 (by
      rw [_root_.mul_inv_rev, mul_inv_cancel_left]
      exact (GQ V).inv_mem hγ))) hΩ z M hM F φ hφ hr

theorem level_of_repr (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))} (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ)
    {F : Lp ℂ 2 (nuQ V μ 𝓕)} {ψ : GA D V → ℂ} (hψ : Continuous ψ) (hr : Repr V μ 𝓕 F ψ) {k : GA D V} (hk : ρ k F = F)
    (g : GA D V) : ψ (g * k) = ψ g := by
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, huniq, -, htr, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h1 := htr F ψ k hr
  rw [hk] at h1
  exact congrFun (huniq F (rTr V k ψ) ψ (hψ.comp (continuous_mul_const k)) hψ h1 hr) g

theorem normInf_nonneg (θ : InfFam D) (V : HSp D) (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem pointwise_growth : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  intro D θ V hθ μ 𝓕 ρ hp hρ U hU
  obtain ⟨S, Ω, C₁, hS, hΩ, hsob⟩ := GlobalTheory.T.local_sobolev_inequality_adelic_unitary D θ V hθ U hU μ hp.haar
  have hcount := GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow D θ V hθ Ω hΩ
  refine hcount.elim fun N hN => ?_
  refine ⟨N, S, hS, fun x => ?_⟩
  refine (hN x).elim fun C₂ hC₂ => ?_
  refine ⟨√|C₁| * |C₂|, fun F ψ hF hlev hψ hr u hu => ?_⟩
  obtain ⟨ψ', hr', haut, hsm, hder⟩ := GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU F hF hlev
  have e : ψ' = ψ := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.1 F ψ' ψ haut.cont hψ hr' hr
  subst e
  have h1 := hsob ψ' hψ (fun k hk hk' => level_of_repr V hp hρ hψ hr (hlev k hk hk')) (fun l hl => (hder l hl).1) hsm (x * u)
  have h2 := fun l hl => integral_le_adelic V hp hΩ (x * u) _ (hC₂ u hu) _ _ (hder l (hS l hl)).1 (hder l (hS l hl)).2
  have h3 := le_of_sums S
    (fun l => ∫ o in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ') (x * u * o)‖ ^ 2 ∂μ)
    (fun l => ‖l.foldr (dL2 θ V ρ) F‖) ‖ψ' (x * u)‖ C₁ C₂ (normInf θ V u) N (normInf_nonneg θ V u)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun _ => norm_nonneg _) h1 h2
  exact h3

end GlobalTheory.SobolevGrowth

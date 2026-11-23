import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingSectionQuotientLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOfExpContinuityStatement

open Set

namespace GlobalTheory.TorusDegree

theorem exists_log_on_square (f : ℝ × ℝ → ℂ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (h0 : ∀ v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f v ≠ 0) :
    ∃ g : ℝ × ℝ → ℂ, Continuous g ∧
      ∀ v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Complex.exp (g v) = f v := by
  let p : ℝ × ℝ → ℝ × ℝ := fun v =>
    ((projIcc (0 : ℝ) 1 zero_le_one v.1 : ℝ), (projIcc (0 : ℝ) 1 zero_le_one v.2 : ℝ))
  have hp : Continuous p :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hm : ∀ v, p v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun v =>
    ⟨(projIcc (0 : ℝ) 1 zero_le_one v.1).2, (projIcc (0 : ℝ) 1 zero_le_one v.2).2⟩
  have hc : Continuous (fun v => f (p v)) := hf.comp_continuous hp hm
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨fun v => f (p v), hc⟩ : C(ℝ × ℝ, ℂ)) (a₀ := 0) (Complex.exp_log (h0 _ (hm 0)))
    (fun v => h0 _ (hm v))
  refine ⟨F, F.continuous, fun v hv => ?_⟩
  have h1 : Complex.exp (F v) = f (p v) := congrFun hF v
  have h2 : p v = v := by
    simp only [p, projIcc_of_mem _ hv.1, projIcc_of_mem _ hv.2]
  rw [h1, h2]

theorem continuousAt_side {B : Type} [TopologicalSpace B] (b₀ : B) {J : Type}
    (O : J → Set (B × ℝ × ℝ)) (s : J → B × ℝ × ℝ → ℂ) (K : Set (ℝ × ℝ)) (V : Set B)
    (hV : V ∈ nhds b₀) (r : B × ℝ × ℝ → ℂ) (hr0 : ∀ q ∈ V ×ˢ K, r q ≠ 0)
    (hr : ∀ i, ContinuousOn (fun q => s i q * r q) (O i ∩ V ×ˢ K))
    (hO : ∀ i, IsOpen (O i)) (hcov : ∀ q, ∃ i, q ∈ O i) (hs0 : ∀ i, ∀ q ∈ O i, s i q ≠ 0)
    (γ : B → ℝ × ℝ → ℂ) (hγc : ∀ b ∈ V, Continuous (γ b))
    (hγ : ∀ b ∈ V, ∀ v ∈ K, Complex.exp (γ b v) = r (b, v))
    (p₀ p₁ : ℝ → ℝ × ℝ) (hp₀ : Continuous p₀) (hp₁ : Continuous p₁)
    (hm₀ : ∀ t ∈ Icc (0 : ℝ) 1, p₀ t ∈ K) (hm₁ : ∀ t ∈ Icc (0 : ℝ) 1, p₁ t ∈ K)
    (A : B × ℝ × ℝ → ℂ) (hA : ∀ b, Continuous (fun v : ℝ × ℝ => A (b, v)))
    (hper : ∀ i b t, (b, p₀ t) ∈ O i → (b, p₁ t) ∈ O i)
    (hco : ∀ i b t, (b, p₀ t) ∈ O i → s i (b, p₀ t) = Complex.exp (A (b, p₀ t)) * s i (b, p₁ t)) :
    ContinuousAt (fun b => (A (b, p₀ 1) + γ b (p₀ 1) - γ b (p₁ 1))
      - (A (b, p₀ 0) + γ b (p₀ 0) - γ b (p₁ 0))) b₀ := by
  refine GlobalTheory.T.log_of_exp_continuity B b₀ V (fun q => A (q.1, p₀ q.2) + γ q.1 (p₀ q.2) - γ q.1 (p₁ q.2)) hV ?_ ?_
  · refine continuousOn_of_locally_continuousOn fun q hq => ?_
    obtain ⟨i, hi⟩ := hcov (q.1, p₀ q.2)
    have c₀ : Continuous (fun q : B × ℝ => (q.1, p₀ q.2)) :=
      continuous_fst.prodMk (hp₀.comp continuous_snd)
    have c₁ : Continuous (fun q : B × ℝ => (q.1, p₁ q.2)) :=
      continuous_fst.prodMk (hp₁.comp continuous_snd)
    refine ⟨(fun q : B × ℝ => (q.1, p₀ q.2)) ⁻¹' O i, (hO i).preimage c₀, hi, ?_⟩
    have m₀ : MapsTo (fun q : B × ℝ => (q.1, p₀ q.2))
        (V ×ˢ Icc (0 : ℝ) 1 ∩ (fun q : B × ℝ => (q.1, p₀ q.2)) ⁻¹' O i) (O i ∩ V ×ˢ K) :=
      fun z hz => ⟨hz.2, hz.1.1, hm₀ _ hz.1.2⟩
    have m₁ : MapsTo (fun q : B × ℝ => (q.1, p₁ q.2))
        (V ×ˢ Icc (0 : ℝ) 1 ∩ (fun q : B × ℝ => (q.1, p₀ q.2)) ⁻¹' O i) (O i ∩ V ×ˢ K) :=
      fun z hz => ⟨hper i _ _ hz.2, hz.1.1, hm₁ _ hz.1.2⟩
    have h := ((hr i).comp c₀.continuousOn m₀).div ((hr i).comp c₁.continuousOn m₁)
      (fun z hz => mul_ne_zero (hs0 i _ (m₁ hz).1) (hr0 _ (m₁ hz).2))
    refine h.congr fun z hz => ?_
    have e₀ := hγ z.1 hz.1.1 _ (hm₀ _ hz.1.2)
    have e₁ := hγ z.1 hz.1.1 _ (hm₁ _ hz.1.2)
    have e₂ := hco i z.1 z.2 hz.2
    have n₁ : s i (z.1, p₁ z.2) ≠ 0 := hs0 i _ (m₁ hz).1
    have n₂ : r (z.1, p₁ z.2) ≠ 0 := hr0 _ (m₁ hz).2
    simp only [Function.comp, Pi.div_apply]
    rw [Complex.exp_sub, Complex.exp_add, e₀, e₁, e₂]
    field_simp
  · intro b hb
    exact ((((hA b).comp hp₀).add ((hγc b hb).comp hp₀)).sub ((hγc b hb).comp hp₁)).continuousOn

theorem eventually_eq_of_exp_eq_one {B : Type} [TopologicalSpace B] (b₀ : B) (n : B → ℂ)
    (hn : ContinuousAt n b₀) (h1 : ∀ b, Complex.exp (n b) = 1) :
    ∀ᶠ b in nhds b₀, n b = n b₀ := by
  have h := Metric.continuousAt_iff'.1 hn 1 one_pos
  filter_upwards [h] with b hb
  have he : Complex.exp (n b - n b₀) = 1 := by rw [Complex.exp_sub, h1, h1, div_one]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 he
  rw [dist_eq_norm, hk] at hb
  have hk0 : k = 0 := by
    by_contra hne
    have h1k : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
      simp [abs_of_pos Real.pi_pos]
    rw [this] at hb
    nlinarith [Real.pi_gt_three]
  rw [hk0] at hk
  simpa [sub_eq_zero] using hk

theorem degree_locally_constant : ∀ (B : Type) [TopologicalSpace B] (b₀ : B) (J : Type) (O : J → Set (B × ℝ × ℝ)) (s : J → B × ℝ × ℝ → ℂ) (α β : B × ℝ × ℝ → ℂ), (∀ i, IsOpen (O i)) → (∀ q, ∃ i, q ∈ O i) → (∀ i b x y, ((b, x + 1, y) ∈ O i ↔ (b, x, y) ∈ O i) ∧ ((b, x, y + 1) ∈ O i ↔ (b, x, y) ∈ O i)) → (∀ i, ∀ q ∈ O i, s i q ≠ 0) → (∀ i b, ContinuousOn (fun v : ℝ × ℝ => s i (b, v)) {v | (b, v) ∈ O i}) → (∀ i j, ContinuousOn (fun q => s i q / s j q) (O i ∩ O j)) → (∀ b, Continuous (fun v : ℝ × ℝ => α (b, v)) ∧ Continuous (fun v : ℝ × ℝ => β (b, v))) → (∀ i b x y, (b, x, y) ∈ O i → s i (b, x, y) = Complex.exp (α (b, x, y)) * s i (b, x + 1, y) ∧ s i (b, x, y) = Complex.exp (β (b, x, y)) * s i (b, x, y + 1)) → ∀ᶠ b in nhds b₀, α (b, 0, 1) - α (b, 0, 0) - (β (b, 1, 0) - β (b, 0, 0)) = α (b₀, 0, 1) - α (b₀, 0, 0) - (β (b₀, 1, 0) - β (b₀, 0, 0)) := by
  intro B _ b₀ J O s α β hO hcov hper hs0 hsc hsq hαβ hco
  obtain ⟨V, hV, r, hr0, hr⟩ := GlobalTheory.T.nonvanishing_section_quotient_limit B b₀ J O s (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (isCompact_Icc.prod isCompact_Icc) hO hcov hs0 (fun i => hsc i b₀) hsq
  have hlog : ∀ b, ∃ g : ℝ × ℝ → ℂ, b ∈ V → Continuous g ∧
      ∀ v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Complex.exp (g v) = r (b, v) := by
    intro b
    by_cases hb : b ∈ V
    swap
    · exact ⟨0, fun h => absurd h hb⟩
    have hc : ContinuousOn (fun v => r (b, v)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
      refine continuousOn_of_locally_continuousOn fun v hv => ?_
      obtain ⟨i, hi⟩ := hcov (b, v)
      have c₀ : Continuous (fun v : ℝ × ℝ => (b, v)) := continuous_const.prodMk continuous_id
      refine ⟨{v | (b, v) ∈ O i}, (hO i).preimage c₀, hi, ?_⟩
      have m₀ : MapsTo (fun v : ℝ × ℝ => (b, v))
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∩ {v | (b, v) ∈ O i})
          (O i ∩ V ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := fun z hz => ⟨hz.2, hb, hz.1⟩
      have h := ((hr i).comp c₀.continuousOn m₀).div ((hsc i b).mono inter_subset_right)
        (fun z hz => hs0 i _ hz.2)
      refine h.congr fun z hz => ?_
      have n₁ : s i (b, z) ≠ 0 := hs0 i _ hz.2
      simp only [Function.comp, Pi.div_apply]
      field_simp
    obtain ⟨g, hg⟩ := exists_log_on_square _ hc (fun v hv => hr0 (b, v) ⟨hb, hv⟩)
    exact ⟨g, fun _ => hg⟩
  choose γ hγ using hlog
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have ha := continuousAt_side b₀ O s _ V hV r hr0 hr hO hcov hs0 γ (fun b hb => (hγ b hb).1)
    (fun b hb => (hγ b hb).2) (fun t => (0, t)) (fun t => (1, t)) (by fun_prop) (by fun_prop)
    (fun t ht => ⟨h0, ht⟩) (fun t ht => ⟨h1, ht⟩) α (fun b => (hαβ b).1)
    (fun i b t h => by simpa using (hper i b 0 t).1.2 h)
    (fun i b t h => by simpa using (hco i b 0 t h).1)
  have hb := continuousAt_side b₀ O s _ V hV r hr0 hr hO hcov hs0 γ (fun b hb => (hγ b hb).1)
    (fun b hb => (hγ b hb).2) (fun t => (t, 0)) (fun t => (t, 1)) (by fun_prop) (by fun_prop)
    (fun t ht => ⟨ht, h0⟩) (fun t ht => ⟨ht, h1⟩) β (fun b => (hαβ b).2)
    (fun i b t h => by simpa using (hper i b t 0).2.2 h)
    (fun i b t h => by simpa using (hco i b t 0 h).2)
  refine eventually_eq_of_exp_eq_one b₀
    (fun b => α (b, 0, 1) - α (b, 0, 0) - (β (b, 1, 0) - β (b, 0, 0))) ?_ ?_
  · convert ha.sub hb using 2 with b
    simp only [Pi.sub_apply]
    ring
  · intro b
    obtain ⟨i, hi⟩ := hcov (b, 0, 0)
    have h10 : (b, (1 : ℝ), (0 : ℝ)) ∈ O i := by simpa using (hper i b 0 0).1.2 hi
    have h01 : (b, (0 : ℝ), (1 : ℝ)) ∈ O i := by simpa using (hper i b 0 0).2.2 hi
    have h11 : (b, (1 : ℝ), (1 : ℝ)) ∈ O i := by simpa using (hper i b 0 1).1.2 h01
    have e₁ := (hco i b 0 0 hi).1
    have e₂ := (hco i b 0 0 hi).2
    have e₃ := (hco i b 0 1 h01).1
    have e₄ := (hco i b 1 0 h10).2
    simp only [zero_add] at e₁ e₂ e₃ e₄
    have n₁ := hs0 i _ h11
    have key : Complex.exp (α (b, 0, 0)) * Complex.exp (β (b, 1, 0))
        = Complex.exp (β (b, 0, 0)) * Complex.exp (α (b, 0, 1)) := by
      apply mul_right_cancel₀ n₁
      rw [mul_assoc, ← e₄, ← e₁, mul_assoc, ← e₃, ← e₂]
    simp only [Complex.exp_sub]
    have := Complex.exp_ne_zero (α (b, 0, 0))
    have := Complex.exp_ne_zero (β (b, 1, 0))
    have := Complex.exp_ne_zero (β (b, 0, 0))
    field_simp
    linear_combination -key

end GlobalTheory.TorusDegree

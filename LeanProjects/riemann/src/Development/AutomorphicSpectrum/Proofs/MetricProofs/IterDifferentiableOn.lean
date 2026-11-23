import Mathlib
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

noncomputable def iter {B V : Type} (h : B × V → V) : ℕ → B × V → V
  | 0, p => p.2
  | k + 1, p => h (p.1, iter h k p)

@[simp] theorem iter_zero {B V : Type} (h : B × V → V) (p : B × V) : iter h 0 p = p.2 := rfl

theorem iter_succ {B V : Type} (h : B × V → V) (k : ℕ) (p : B × V) :
    iter h (k + 1) p = h (p.1, iter h k p) := rfl

section Norms

variable {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]

theorem norm_iter_le (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ := by
  have key : ∀ k : ℕ, ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ ∧ iter h k (b, s) ∈ ball (0 : V) ρ := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      simpa using hs
    | succ k ih =>
      have hk := hcontr b hb _ ih.2
      have e : iter h (k + 1) (b, s) = h (b, iter h k (b, s)) := rfl
      rw [e]
      refine ⟨?_, ?_⟩
      · calc ‖h (b, iter h k (b, s))‖ ≤ 3 / 5 * ‖iter h k (b, s)‖ := hk
          _ ≤ 3 / 5 * ((3 / 5) ^ k * ‖s‖) := by gcongr; exact ih.1
          _ = (3 / 5) ^ (k + 1) * ‖s‖ := by ring
      · have h2 := mem_ball_zero_iff.mp ih.2
        rw [mem_ball_zero_iff]
        nlinarith [norm_nonneg (iter h k (b, s))]
  exact (key k).1

theorem iter_mem_ball (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    iter h k (b, s) ∈ ball (0 : V) ρ := by
  rw [mem_ball_zero_iff]
  have h1 := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : (3 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : ‖s‖ < ρ := mem_ball_zero_iff.mp hs
  nlinarith [norm_nonneg s]

end Norms

theorem iter_differentiableOn {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hd : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : V) ρ))
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) (k : ℕ) :
    DifferentiableOn ℂ (iter h k) (ball b₀ ρ ×ˢ ball (0 : V) ρ) := by
  induction k with
  | zero =>
    have e : iter h 0 = Prod.snd := funext fun p => rfl
    rw [e]
    exact differentiableOn_snd
  | succ k ih =>
    have e : iter h (k + 1) = h ∘ fun p => (p.1, iter h k p) := funext fun p => rfl
    rw [e]
    refine hd.comp (differentiableOn_fst.prodMk ih) ?_
    intro p hp
    exact Set.mk_mem_prod hp.1 (iter_mem_ball b₀ h ρ hcontr hp.1 hp.2 k)

theorem medial_eventually {B V : Type} [TopologicalSpace B] [Zero V] [TopologicalSpace V] (b₀ : B)
    (μ : B × V × V → V) (hc : ContinuousAt μ (b₀, 0, 0)) (h0 : μ (b₀, 0, 0) = 0)
    (hcomm : ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1))
    (hassoc : ∀ᶠ p : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) :
    ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.1), μ (p.1, p.2.2, p.2.2)) = μ (p.1, μ p, μ p) := by
  have hfst : Tendsto (fun p : B × V × V => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) := continuous_fst.tendsto _
  have hs : Tendsto (fun p : B × V × V => p.2.1) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_fst.comp continuous_snd).tendsto _
  have ht : Tendsto (fun p : B × V × V => p.2.2) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_snd.comp continuous_snd).tendsto _
  have hμ : Tendsto μ (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    have := hc.tendsto
    rwa [h0] at this
  have htt : Tendsto (fun p : B × V × V => μ (p.1, p.2.2, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    hμ.comp (hfst.prodMk_nhds (ht.prodMk_nhds ht))
  have orbitMap_conj_smul_one := (hfst.prodMk_nhds (hs.prodMk_nhds (hs.prodMk_nhds htt))).eventually hassoc
  have orbitMap_conj_smul_two := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds ht))).eventually hassoc
  have selfLieBasisVector := (hfst.prodMk_nhds (ht.prodMk_nhds (hs.prodMk_nhds ht))).eventually hassoc
  have eA4 := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds hμ))).eventually hassoc
  filter_upwards [orbitMap_conj_smul_one, orbitMap_conj_smul_two, selfLieBasisVector, eA4, hcomm] with ⟨b, s, t⟩ a1 a2 a3 a4 c
  dsimp only at a1 a2 a3 a4 c ⊢
  calc μ (b, μ (b, s, s), μ (b, t, t)) = μ (b, s, μ (b, s, μ (b, t, t))) := a1
    _ = μ (b, s, μ (b, μ (b, s, t), t)) := by rw [a2]
    _ = μ (b, s, μ (b, μ (b, t, s), t)) := by rw [c]
    _ = μ (b, s, μ (b, t, μ (b, s, t))) := by rw [a3]
    _ = μ (b, μ (b, s, t), μ (b, s, t)) := a4.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

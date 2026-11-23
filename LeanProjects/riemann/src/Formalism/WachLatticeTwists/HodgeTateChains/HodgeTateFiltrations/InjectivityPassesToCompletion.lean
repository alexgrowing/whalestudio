import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem injectivity_passes_to_completion : InjectivityPassesToCompletion := by
  intro R _ Xm _ _ ϖ z hc hz X0 g hdense hsat hstab hinj0 hsur0

  have huniq : ∀ p ∈ X0, ∀ q ∈ X0, g p - p = g q - q → p = q := by
    intro p hp q hq h
    have h1 : g (p - q) = p - q := by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, add_comm (p) (g q)]
      have := sub_eq_sub_iff_add_eq_add.1 h
      rw [this]
    exact sub_eq_zero.1 (hinj0 _ (X0.sub_mem hp hq) h1)

  have key : ∀ (n : ℕ) (v' : Xm) (y : Xm), (ϖ ^ n) • v' ∈ X0 → y ∈ X0 →
      z • ((ϖ ^ n) • v') = g y - y → ∃ t, y = (ϖ ^ n) • t := by
    intro n v' y hv hy hzy
    obtain ⟨t, ht, hvt⟩ := hsat n v' hv
    obtain ⟨yt, hyt, hzt⟩ := hsur0 t ht
    refine ⟨yt, huniq _ hy _ (X0.smul_mem _ hyt) ?_⟩
    rw [← hzy, hvt, map_smul, ← smul_sub, ← hzt, smul_comm]
  constructor
  · intro x hx
    apply hz
    apply haus_of ϖ hc
    intro n
    obtain ⟨x0, hx0, x', hxx⟩ := hdense x n
    have h1 : g x0 - x0 = (ϖ ^ n) • (x' - g x') := by
      have h2 : g x - x = 0 := sub_eq_zero.2 hx
      rw [hxx, map_add, map_smul] at h2
      rw [smul_sub]
      have h3 : g x0 - x0 = (g x0 + ϖ ^ n • g x' - (x0 + ϖ ^ n • x')) + (ϖ ^ n • x' - ϖ ^ n • g x') := by
        abel
      rw [h3, h2, zero_add]
    have hmem : (ϖ ^ n) • (x' - g x') ∈ X0 := by
      rw [← h1]; exact X0.sub_mem (hstab _ hx0) hx0
    obtain ⟨t, ht⟩ := key n (x' - g x') (z • x0) hmem (X0.smul_mem _ hx0)
      (by rw [← h1, map_smul, smul_sub])
    refine ⟨t + z • x', ?_⟩
    rw [hxx, smul_add, ht, smul_add, smul_comm z (ϖ ^ n)]
  · intro x
    choose a ha b hab using hdense x
    choose y hy hzy using fun n => hsur0 (a n) (ha n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        y m ≡ y n [SMOD ((Ideal.span {ϖ}) ^ m • (⊤ : Submodule R Xm))] := by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top]
      have h1 : a m - a n = (ϖ ^ m) • ((ϖ ^ (n - m)) • b n - b m) := by
        rw [smul_sub, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
        have e1 := hab m
        have e2 := hab n
        have e3 : a m + ϖ ^ m • b m = a n + ϖ ^ n • b n := by rw [← e1, ← e2]
        rw [sub_eq_sub_iff_add_eq_add, e3, add_comm]
      have hmem : (ϖ ^ m) • ((ϖ ^ (n - m)) • b n - b m) ∈ X0 := by
        rw [← h1]; exact X0.sub_mem (ha m) (ha n)
      exact key m _ (y m - y n) hmem (X0.sub_mem (hy m) (hy n))
        (by rw [← h1, smul_sub, hzy m, hzy n, map_sub]; abel)
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    apply sub_eq_zero.1
    apply haus_of ϖ hc
    intro n
    have h1 := hL n
    rw [SModEq.sub_mem, mem_pow_smul_top] at h1
    obtain ⟨t, ht⟩ := h1
    have hLy : L = y n - ϖ ^ n • t := by rw [← ht]; abel
    refine ⟨z • b n + (g t - t), ?_⟩
    rw [hLy, map_sub, map_smul]
    conv_lhs => rw [hab n]
    rw [smul_add, hzy n, smul_add, smul_sub, smul_comm z (ϖ ^ n)]
    abel

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] {I : Ideal R} {J J' : Ideal B} {L : Ideal C}

theorem Sup.one_mem_fil (δ : DividedPowers J) : (1 : B) ∈ fil δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem Sup.dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem Sup.fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨l, h1, h2, rfl⟩, _, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', fun p hp ↦ ?_, ?_, by simp⟩
  · rcases List.mem_append.1 hp with h | h
    exacts [h1 p h, h1' p h]
  · simp only [List.map_append, List.sum_append]; omega

theorem Sup.exists_fil_eq_bot {δ : DividedPowers J} (h : IsNilDP δ) : ∃ N, ∀ n, N ≤ n → fil δ n = ⊥ := by
  obtain ⟨N, h⟩ := h
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [fil, Ideal.span_eq_bot]
  rintro _ ⟨l, h1, h2, rfl⟩
  exact h l h1 (hn.trans h2)

theorem Sup.isPDNilpotent_of_family (δ : DividedPowers J) (s : Set B) (hs : J = Ideal.span s) (F : ℕ → Ideal B)
    (h0 : (1 : B) ∈ F 0) (hm : ∀ m n, F m * F n ≤ F (m + n)) (hg : ∀ x ∈ s, ∀ n, δ.dpow n x ∈ F n)
    (N : ℕ) (hN : ∀ n, N ≤ n → F n = ⊥) : IsNilDP δ := by
  subst hs
  have hdp : ∀ y ∈ Ideal.span s, ∀ n, δ.dpow n y ∈ F n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hg x hx
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [δ.dpow_zero (Ideal.zero_mem _)]; exact h0
      · rw [δ.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hm _ _ (Ideal.mul_mem_mul (ihx k.1) (ihy k.2))
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ Ideal.span s) →
      (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ F (l.map Prod.fst).sum := by
    intro l hl
    induction l with
    | nil => exact h0
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hm _ _ (Ideal.mul_mem_mul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq])))
  refine ⟨N, fun l hl h ↦ ?_⟩
  have := hprod l hl
  rwa [hN _ h, Ideal.mem_bot] at this

theorem Sup.sup_map_eq_span (f : R →+* B) : J ⊔ I.map f = Ideal.span ((J : Set B) ∪ f '' I) := by
  rw [Ideal.span_union, Ideal.span_eq]; rfl

theorem nil_sup (κ : DividedPowers I) (δ : DividedPowers J) (f : R →+* B) (δ' : DividedPowers J')
    (hJ : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B)) (h₂ : IsDPMorphism κ δ' f)
    (hκ : IsNilDP κ) (hδ : IsNilDP δ) : IsNilDP δ' := by
  obtain ⟨N₁, k₁⟩ := Sup.exists_fil_eq_bot hκ
  obtain ⟨N₂, k₂⟩ := Sup.exists_fil_eq_bot hδ
  let F : ℕ → Ideal B := fun n ↦ ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = n}, (fil κ p.1.1).map f * fil δ p.1.2
  have hF : ∀ a b n, a + b = n → (fil κ a).map f * fil δ b ≤ F n := fun a b n h ↦
    le_iSup (fun p : {p : ℕ × ℕ // p.1 + p.2 = n} ↦ (fil κ p.1.1).map f * fil δ p.1.2) ⟨(a, b), h⟩
  have one : (1 : B) ∈ (fil κ 0).map f := by
    simpa using Ideal.mem_map_of_mem f (Sup.one_mem_fil κ)
  refine Sup.isPDNilpotent_of_family δ' _ (hJ.trans (Sup.sup_map_eq_span f)) F ?_ (fun m n ↦ ?_) ?_ (N₁ + N₂) fun n hn ↦ ?_
  · simpa using hF 0 0 0 rfl (Ideal.mul_mem_mul one (Sup.one_mem_fil δ))
  · simp only [F, Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
    rintro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩
    refine le_trans ?_ (hF (c + a) (d + b) _ (by simp only at h h'; omega))
    rw [mul_mul_mul_comm, ← Ideal.map_mul]
    exact Ideal.mul_mono (Ideal.map_mono (Sup.fil_mul_le _ _ _)) (Sup.fil_mul_le _ _ _)
  · rintro x (hx | ⟨r, hr, rfl⟩) n
    · have := h₁.2 (n := n) x hx
      simp only [RingHom.id_apply] at this
      rw [this]
      simpa using hF 0 n n (zero_add n) (Ideal.mul_mem_mul one (Sup.dpow_mem_fil δ hx n))
    · rw [h₂.2 r hr]
      simpa using hF n 0 n rfl (Ideal.mul_mem_mul (Ideal.mem_map_of_mem f (Sup.dpow_mem_fil κ hr n)) (Sup.one_mem_fil δ))
  · simp only [F, iSup_eq_bot]
    rintro ⟨⟨a, b⟩, h⟩
    simp only at h ⊢
    by_cases ha : N₁ ≤ a
    · rw [k₁ a ha, Ideal.map_bot, Ideal.bot_mul]
    · rw [k₂ b (by omega), Ideal.mul_bot]

theorem isDPMorphism_sup (κ : DividedPowers I) (δ : DividedPowers J) (f : R →+* B) (δ' : DividedPowers J')
    (hJ : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B)) (h₂ : IsDPMorphism κ δ' f)
    (θ : DividedPowers L) (g : B →+* C) (k₁ : IsDPMorphism δ θ g) (k₂ : IsDPMorphism κ θ (g.comp f)) :
    IsDPMorphism δ' θ g := by
  refine IsDPMorphism.on_span δ' θ (hJ.trans (Sup.sup_map_eq_span f)) ?_ ?_
  · rintro x (hx | ⟨r, hr, rfl⟩)
    · exact k₁.1 (Ideal.mem_map_of_mem _ hx)
    · exact k₂.1 (Ideal.mem_map_of_mem _ hr)
  · rintro n x (hx | ⟨r, hr, rfl⟩)
    · have := h₁.2 (n := n) x hx
      simp only [RingHom.id_apply] at this
      rw [this]
      exact (k₁.2 x hx).symm
    · rw [h₂.2 r hr]
      exact (k₂.2 r hr).symm

end FubiniStudyChowHeightFormula₂.Adr

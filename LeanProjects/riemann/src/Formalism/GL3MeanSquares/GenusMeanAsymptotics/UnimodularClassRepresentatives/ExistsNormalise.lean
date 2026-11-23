import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandG

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

variable {𝔭 : Ideal (𝓞 F)}

theorem symm0 {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  have e : starRingEnd K (h x y) = h y x := by
    first
    | exact hs.eq x y
    | exact hs x y
  rw [hxy, map_zero] at e
  exact e.symm

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (μ ν : K) (x y : V) :
    h (μ • x) (ν • y) = star μ * ν * h x y := by
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply]
  ring

theorem exists_normalise (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {e : V} (he : e ≠ 0) :
    ∃ μ : K, ∃ a : 𝓞 F, h (μ • e) (μ • e) = κ (ι a) ∧ a ∉ 𝔭 ^ 2 := by
  have hd0 : h e e ≠ 0 := fun h0 => he (han e h0)
  have hds : star (h e e) = h e e := by
    have e' : starRingEnd K (h e e) = h e e := by
      first
      | exact hs.eq e e
      | exact hs e e
    rwa [starRingEnd_apply] at e'
  obtain ⟨μ, -, hμs, a, ha, ha2⟩ := exists_scale_fixed hF h𝔭 hd0 hds
  exact ⟨μ, a, by rw [form_smul_smul, hμs, ha], ha2⟩

theorem exists_pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {z e : V} {c a : 𝓞 F} (hze : h z e = 0)
    (hz : h z z = κ (ι c)) (he : h e e = κ (ι a)) (hc2 : c ∉ 𝔭 ^ 2) (ha2 : a ∉ 𝔭 ^ 2) (hcp : c ∈ 𝔭)
    (hap : a ∈ 𝔭) :
    ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧ b₂ ∉ 𝔭 ^ 2 ∧
      h w u = 0 ∧ ∀ v, h z v = 0 → h e v = 0 → h u v = 0 ∧ h w v = 0 := by
  have hez := symm0 hs hze
  obtain ⟨α, ν, hν, hW2, hW3⟩ := exists_alpha hK hF h𝔭 hcp hc2 hap ha2
  have hν' : star (κ α) * κ α = κ (ι ν) := by rw [← hν, map_mul]; rfl
  set W := c * ν + a with hW
  have hW0 : W ≠ 0 := fun h0 => hW3 (h0 ▸ zero_mem _)
  have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ zero_mem _)
  have ha0 : a ≠ 0 := fun h0 => ha2 (h0 ▸ zero_mem _)
  obtain ⟨μ₁, -, hμ₁s, b₁, hb₁, hb₁'⟩ := exists_scale (K := K) (r := 1) (k := 0) hF h𝔭
    (by simpa using hW2) (by simpa using hW3)
  obtain ⟨μ₂, -, hμ₂s, b₂, hb₂, hb₂'⟩ := exists_scale_int (K := K) hF h𝔭
    (mul_ne_zero (mul_ne_zero hc0 ha0) hW0)
  have hsι : ∀ t : 𝓞 F, star (κ (ι t)) = κ (ι t) := star_ι hF
  refine ⟨μ₁ • (κ α • z + e), μ₂ • ((-κ (ι a)) • z + (star (κ α) * κ (ι c)) • e), b₁, b₂,
    ?_, ?_, by simpa using hb₁', hb₂', ?_, fun v hzv hev => ⟨?_, ?_⟩⟩
  · rw [form_smul_smul, hμ₁s, ← hb₁]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul]
    linear_combination κ (ι c) * hν'
  · rw [form_smul_smul, hμ₂s, ← hb₂]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, hW, map_mul, star_neg, star_star, hsι]
    linear_combination (κ (ι c) * κ (ι c) * κ (ι a)) * hν'
  · rw [form_smul_smul]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hz, he, hze, hez, star_neg, star_mul', star_star, hsι]
    ring
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzv, hev, mul_zero, add_zero]

theorem κι_inj {a b : 𝓞 F} (hab : κ (ι a) = κ (ι b)) : a = b := by
  have e : ∀ c : 𝓞 F, κ (ι c) = algebraMap F K (c : F) := fun c => rfl
  rw [e, e] at hab
  exact RingOfIntegers.ext ((algebraMap F K).injective hab)

variable [FiniteDimensional K V]

theorem exists_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (han : ∀ x, h x x = 0 → x = 0) {x₀ : V} {n : 𝓞 F}
    (hx : h x₀ x₀ = κ (ι n)) (hn : n ∉ 𝔭) :
    ∀ r : ℕ, r + 1 ≤ finrank K V → ∃ (y : Fin r → V) (a : Fin r → 𝓞 F) (z : V) (c : 𝓞 F),
      (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ (∀ i, h z (y i) = 0) ∧
      (∀ i, h (y i) (y i) = κ (ι (a i))) ∧ h z z = κ (ι c) ∧ (∏ i, a i) ∉ 𝔭 ∧ c ∉ 𝔭 ^ 2 ∧
      (z = x₀ ∨ ∃ i, y i = x₀) := by
  have hp := h𝔭.isPrime
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨fun i => i.elim0, fun i => i.elim0, x₀, n, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, hx, ?_, fun hm => hn (Ideal.pow_le_self two_ne_zero hm), Or.inl rfl⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  | succ r ih =>
    intro hr
    obtain ⟨y, a, z, c, ho, hzy, hny, hnz, hprod, hc2, hx₀⟩ := ih (by omega)
    obtain ⟨e₀, he₀, hoe⟩ := GramDeterminantPositive.exists_ortho_ne_zero h (Fin.cons z y : Fin (r + 1) → V)
      (by omega)
    obtain ⟨μ, ae, hne, hae2⟩ := exists_normalise hF h𝔭 hs han he₀
    have hze : h z (μ • e₀) = 0 := by
      have := hoe 0
      rw [Fin.cons_zero] at this
      rw [map_smul, this, smul_zero]
    have hye : ∀ i, h (y i) (μ • e₀) = 0 := fun i => by
      have := hoe i.succ
      rw [Fin.cons_succ] at this
      rw [map_smul, this, smul_zero]
    set e := μ • e₀ with he
    have key : ∃ u w : V, ∃ b₁ b₂ : 𝓞 F, h u u = κ (ι b₁) ∧ h w w = κ (ι b₂) ∧ b₁ ∉ 𝔭 ∧
        b₂ ∉ 𝔭 ^ 2 ∧ h w u = 0 ∧ (∀ i, h u (y i) = 0 ∧ h w (y i) = 0) ∧
        (u = x₀ ∨ ∃ i, y i = x₀) := by
      by_cases hcp : c ∈ 𝔭
      · have hx₀' : ∃ i, y i = x₀ := by
          rcases hx₀ with rfl | h1
          · exact absurd hcp (by rw [κι_inj (hnz.symm.trans hx)]; exact hn)
          · exact h1
        by_cases hap : ae ∈ 𝔭
        · obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6⟩ :=
            exists_pair hK hF h𝔭 hs hze hnz hne hc2 hae2 hcp hap
          exact ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5,
            fun i => h6 _ (hzy i) (symm0 hs (hye i)), Or.inr hx₀'⟩
        · exact ⟨e, z, ae, c, hne, hnz, hap, hc2, hze,
            fun i => ⟨symm0 hs (hye i), hzy i⟩, Or.inr hx₀'⟩
      · exact ⟨z, e, c, ae, hnz, hne, hcp, hae2, symm0 hs hze,
          fun i => ⟨hzy i, symm0 hs (hye i)⟩, hx₀⟩
    obtain ⟨u, w, b₁, b₂, h1, h2, h3, h4, h5, h6, h7⟩ := key
    refine ⟨Fin.cons u y, Fin.cons b₁ a, w, b₂, ?_, ?_, ?_, h2, ?_, h4, Or.inr ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact (h6 j).1
      · intro _; rw [Fin.cons_zero, Fin.cons_succ]; exact symm0 hs (h6 i).1
      · intro hij
        rw [Fin.cons_succ, Fin.cons_succ]
        exact ho i j fun hh => hij (by rw [hh])
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero]; exact h5
      · rw [Fin.cons_succ]; exact (h6 i).2
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero, Fin.cons_zero]; exact h1
      · rw [Fin.cons_succ, Fin.cons_succ]; exact hny i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact fun hm => (hp.mem_or_mem hm).elim h3 hprod
    · rcases h7 with rfl | ⟨i, hi⟩
      · exact ⟨0, by rw [Fin.cons_zero]⟩
      · exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩

end Formalism.HermitianLattices.Ext.L3.Cell

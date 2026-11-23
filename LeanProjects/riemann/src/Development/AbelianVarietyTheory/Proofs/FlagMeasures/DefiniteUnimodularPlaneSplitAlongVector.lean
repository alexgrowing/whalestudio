import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.PlaneSplit

variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [NumberField E] in
theorem int_star {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd E).toIntAlgHom

omit [NumberField E] [StarRing E] in
theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨s, hs⟩ => hs ▸ s.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem one_induction (P N : Submodule (𝓞 E) E) (β : E) (hβ : star β = β) (hβ0 : β ≠ 0) (hfg : P.FG)
    (hne : P ≠ ⊥) (hN : ∀ t, t ∈ N ↔ ∀ a ∈ P, IsIntegral ℤ (star a * β * t)) (Q : E → Prop)
    (hadd : ∀ a b, Q a → Q b → Q (a + b)) (hQ : ∀ x ∈ N, ∀ a ∈ P, Q (star x * β * a)) : Q 1 := by
  let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨P, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := fun h => hne (FractionalIdeal.coeToSubmodule_eq_bot.2 h)
  have h1 : (1 : E) ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (I : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, inv_mul_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  refine Submodule.mul_induction_on h1 (fun z hz a ha => ?_) hadd
  have hz' := (FractionalIdeal.mem_inv_iff hI).1 hz
  have hx : star z / β ∈ N := by
    rw [hN]
    intro b hb
    have h2 := hz' b hb
    rw [FractionalIdeal.mem_one_iff] at h2
    obtain ⟨s, hs⟩ := h2
    have h3 : IsIntegral ℤ (z * b) := hs ▸ s.2
    have e : star b * β * (star z / β) = star (z * b) := by
      rw [star_mul]; field_simp
    rw [e]; exact int_star h3
  have := hQ _ hx a ha
  have e : star (star z / β) * β * a = z * a := by
    rw [star_div₀, star_star, hβ]; field_simp
  rwa [e] at this

theorem span_eq_colon (P N : Submodule (𝓞 E) E) (β : E) (hβ : star β = β) (hβ0 : β ≠ 0) (hfg : P.FG)
    (hne : P ≠ ⊥) (hN : ∀ t, t ∈ N ↔ ∀ a ∈ P, IsIntegral ℤ (star a * β * t)) (c : E) :
    c ∈ Submodule.span (𝓞 E) {t | ∃ x ∈ N, ∃ y ∈ N, t = star x * β * y} ↔ ∀ a ∈ P, c * a ∈ N := by
  constructor
  · intro hc
    induction hc using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ht
      intro a ha
      rw [hN]
      intro b hb
      have h1 := (hN y).1 hy b hb
      have h2 := int_star ((hN x).1 hx a ha)
      have e : star b * β * (star x * β * y * a) = (star b * β * y) * star (star a * β * x) := by
        simp only [star_mul, star_star, hβ]; ring
      rw [e]; exact h1.mul h2
    | zero => intro a _; simp
    | add s t _ _ hs ht => intro a ha; rw [add_mul]; exact N.add_mem (hs a ha) (ht a ha)
    | smul r t _ ht => intro a ha; rw [smul_mul_assoc]; exact N.smul_mem r (ht a ha)
  · intro hc
    have := one_induction P N β hβ hβ0 hfg hne hN
      (fun e => c * e ∈ Submodule.span (𝓞 E) {t | ∃ x ∈ N, ∃ y ∈ N, t = star x * β * y})
      (fun a b ha hb => by rw [mul_add]; exact Submodule.add_mem _ ha hb)
      (fun x hx a ha => Submodule.subset_span ⟨x, hx, c * a, hc a ha, by ring⟩)
    simpa using this

theorem dual_ne_bot (P N : Submodule (𝓞 E) E) (β : E) (hβ : star β = β) (hβ0 : β ≠ 0) (hfg : P.FG)
    (hne : P ≠ ⊥) (hN : ∀ t, t ∈ N ↔ ∀ a ∈ P, IsIntegral ℤ (star a * β * t)) : N ≠ ⊥ := by
  intro h
  have := one_induction P N β hβ hβ0 hfg hne hN (fun e => e = 0)
    (fun a b ha hb => by rw [ha, hb, add_zero])
    (fun x hx a _ => by rw [h, Submodule.mem_bot] at hx; simp [hx])
  exact one_ne_zero this

theorem exists_good (P N : Submodule (𝓞 E) E) (β : E) (hβ : star β = β) (hβ0 : β ≠ 0) (hfg : P.FG)
    (hne : P ≠ ⊥) (hN : ∀ t, t ∈ N ↔ ∀ a ∈ P, IsIntegral ℤ (star a * β * t))
    (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ x ∈ N, ∃ a ∈ P, ∃ b ∈ P, star x * β * a ∉ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔭 ∧
      star b * β * x ∉ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔭 := by
  set M := Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔭 with hM
  have h1 : (1 : E) ∉ M := by
    rintro ⟨s, hs, h⟩
    have : s = 1 := by
      apply IsFractionRing.injective (𝓞 E) E
      simpa using h
    exact h𝔭 ((Ideal.eq_top_iff_one _).2 (this ▸ hs))
  have hA : ∃ x ∈ N, ∃ a ∈ P, star x * β * a ∉ M := by
    by_contra h
    push Not at h
    exact h1 (one_induction P N β hβ hβ0 hfg hne hN (fun e => e ∈ M) (fun a b => M.add_mem) h)
  have hB : ∃ x ∈ N, ∃ a ∈ P, star a * β * x ∉ M := by
    by_contra h
    push Not at h
    have := one_induction P N β hβ hβ0 hfg hne hN (fun e => star e ∈ M)
      (fun a b ha hb => by rw [star_add]; exact M.add_mem ha hb)
      (fun x hx a ha => by
        have e : star (star x * β * a) = star a * β * x := by
          simp only [star_mul, star_star, hβ]; ring
        rw [e]; exact h x hx a ha)
    exact h1 (by simpa using this)
  obtain ⟨x, hx, a, ha, hxa⟩ := hA
  obtain ⟨y, hy, b, hb, hyb⟩ := hB
  by_cases h2 : star b * β * x ∈ M
  · by_cases h3 : star y * β * a ∈ M
    · refine ⟨x + y, N.add_mem hx hy, a, ha, b, hb, fun h => hxa ?_, fun h => hyb ?_⟩
      · have := M.sub_mem h h3
        convert this using 1
        rw [star_add]; ring
      · have := M.sub_mem h h2
        convert this using 1
        ring
    · exact ⟨y, hy, a, ha, b, hb, h3, hyb⟩
  · exact ⟨x, hx, a, ha, b, hb, hxa, h2⟩

theorem eq_span_fixed (P N : Submodule (𝓞 E) E) (β : E) (hβ : star β = β) (hβ0 : β ≠ 0) (hfg : P.FG)
    (hne : P ≠ ⊥) (hN : ∀ t, t ∈ N ↔ ∀ a ∈ P, IsIntegral ℤ (star a * β * t)) (𝔫 : Ideal (𝓞 E))
    (h𝔫 : Submodule.span (𝓞 E) {t | ∃ x ∈ N, ∃ y ∈ N, t = star x * β * y} =
      Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫) :
    𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} := by
  set 𝔟 : Ideal (𝓞 E) := Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} with h𝔟
  refine le_antisymm ?_ (Ideal.span_le.2 fun t ht => ht.1)
  have inj := IsFractionRing.injective (𝓞 E) E
  have htop : Submodule.colon 𝔟 (𝔫 : Set (𝓞 E)) = ⊤ := by
    by_contra hne'
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal _ hne'
    obtain ⟨x, hx, a, ha, b, hb, h1, h2⟩ := exists_good P N β hβ hβ0 hfg hne hN 𝔭 h𝔭.ne_top
    have e1 : ∀ z c, star z * β * c = star (star c * β * z) := fun z c => by
      simp only [star_mul, star_star, hβ]; ring
    have i1 : IsIntegral ℤ (star x * β * a) := by rw [e1]; exact int_star ((hN x).1 hx a ha)
    have i2 : IsIntegral ℤ (star b * β * x) := (hN x).1 hx b hb
    let s : 𝓞 E := ⟨_, i1⟩
    let s' : 𝓞 E := ⟨_, i2⟩
    have hs : s ∉ 𝔭 := fun h => h1 ⟨s, h, rfl⟩
    have hs' : s' ∉ 𝔭 := fun h => h2 ⟨s', h, rfl⟩
    have hss : s * s' ∈ Submodule.colon 𝔟 (𝔫 : Set (𝓞 E)) := by
      rw [Submodule.mem_colon]
      intro t ht
      have hx𝔫 : star x * β * x ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 := by
        rw [← h𝔫]; exact Submodule.subset_span ⟨x, hx, x, hx, rfl⟩
      obtain ⟨n, hn, hnx⟩ := hx𝔫
      have hnx' : (n : E) = star x * β * x := hnx
      have hn𝔟 : n ∈ 𝔟 := Ideal.subset_span ⟨hn, by rw [hnx', ← e1]⟩
      have key : ∀ e ∈ Submodule.span (𝓞 E) {t | ∃ x ∈ N, ∃ y ∈ N, t = star x * β * y},
          (s * s') • e ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔟 := by
        intro e he
        induction he using Submodule.span_induction with
        | mem e he =>
          obtain ⟨y, hy, z, hz, rfl⟩ := he
          have j1 : IsIntegral ℤ (star y * β * a) := by rw [e1]; exact int_star ((hN y).1 hy a ha)
          have j2 : IsIntegral ℤ (star b * β * z) := (hN z).1 hz b hb
          let r : 𝓞 E := ⟨_, j1.mul j2⟩
          refine ⟨r * n, 𝔟.mul_mem_left _ hn𝔟, ?_⟩
          change (star y * β * a) * (star b * β * z) * (n : E) =
            (star x * β * a) * (star b * β * x) * (star y * β * z)
          rw [hnx']; ring
        | zero => simp
        | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
        | smul r e _ he => rw [smul_comm]; exact Submodule.smul_mem _ r he
      obtain ⟨m, hm, hme⟩ := key (t : E) (by rw [h𝔫]; exact ⟨t, ht, rfl⟩)
      have : m = (s * s') • t := inj (by
        change _ = ((s * s' * t : 𝓞 E) : E)
        exact hme)
      exact this ▸ hm
    rcases h𝔭.isPrime.mem_or_mem (hle hss) with h | h
    exacts [hs h, hs' h]
  intro t ht
  have h1 : (1 : 𝓞 E) ∈ Submodule.colon 𝔟 (𝔫 : Set (𝓞 E)) := htop ▸ Submodule.mem_top
  simpa using Submodule.mem_colon.1 h1 t ht

omit [StarRing E] in
theorem isLattice_of (N : Submodule (𝓞 E) E) (hfg : N.FG) (hne : N ≠ ⊥) : Submodule.IsLattice E N where
  fg := hfg
  span_eq_top := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [eq_top_iff]
    intro y _
    have : y = (y / x) • x := by rw [smul_eq_mul]; field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

omit [StarRing E] in
theorem absNorm_le (hE : IsTotallyComplex E) (𝔫 : Ideal (𝓞 E)) (b : 𝓞 E) (hb : b ∈ 𝔫) (hb0 : b ≠ 0) (ρ : ℝ)
    (hρ : ∀ φ : E →+* ℂ, ‖φ (b : E)‖ ≤ ρ) : (Ideal.absNorm 𝔫 : ℝ) ≤ ρ ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  have h1 : Ideal.absNorm 𝔫 ∣ Ideal.absNorm (Ideal.span {b}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hb)
  have h2 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have h3 : (Ideal.absNorm 𝔫 : ℝ) ≤ (Ideal.absNorm (Ideal.span {b}) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
  refine h3.trans ?_
  rw [Ideal.absNorm_span_singleton]
  have h4 : ((Algebra.norm ℤ b).natAbs : ℝ) = |(Algebra.norm ℚ (b : E) : ℝ)| := by
    rw [← Algebra.coe_norm_int, Nat.cast_natAbs]; simp
  rw [h4, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm, pow_mul, Formalism.HermitianLatticesTheory.fDeg, ← Finset.card_univ,
    ← Finset.prod_const]
  refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
  rw [IsTotallyComplex.mult_eq]
  have : w (b : E) ≤ ρ := by rw [← InfinitePlace.norm_embedding_eq]; exact hρ _
  gcongr

theorem diag_split (β₁ β₂ : E) (h1 : star β₁ = β₁) (h2 : star β₂ = β₂) (h10 : β₁ ≠ 0) (h20 : β₂ ≠ 0)
    (L : Submodule (𝓞 E) (E × E)) (hfg : L.FG) (hp : ∃ x ∈ L, x.1 ≠ 0) (hq : ∃ x ∈ L, x.2 ≠ 0)
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2)) :
    ∃ (A B : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), Submodule.IsLattice E A ∧ Submodule.IsLattice E B ∧
      (∀ t, t ∈ A ↔ (t, 0) ∈ L) ∧ (∀ t, t ∈ B ↔ (0, t) ∈ L) ∧
      Submodule.span (𝓞 E) {t | ∃ x ∈ A, ∃ y ∈ A, t = star x * β₁ * y} =
        Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧
      Submodule.span (𝓞 E) {t | ∃ x ∈ B, ∃ y ∈ B, t = star x * β₂ * y} =
        Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧
      𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} := by
  let A := L.comap (LinearMap.inl (𝓞 E) E E)
  let B := L.comap (LinearMap.inr (𝓞 E) E E)
  let P := L.map (LinearMap.fst (𝓞 E) E E)
  let Q := L.map (LinearMap.snd (𝓞 E) E E)
  have hA : ∀ t, t ∈ A ↔ (t, 0) ∈ L := fun t => Iff.rfl
  have hB : ∀ t, t ∈ B ↔ (0, t) ∈ L := fun t => Iff.rfl
  have hPfg : P.FG := hfg.map _
  have hQfg : Q.FG := hfg.map _
  have hPne : P ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := hp
    exact fun h => hx0 ((Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩)
  have hQne : Q ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := hq
    exact fun h => hx0 ((Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩)
  have hAP : ∀ t, t ∈ A ↔ ∀ a ∈ P, IsIntegral ℤ (star a * β₁ * t) := by
    intro t
    rw [hA, hL]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      simpa using h y hy
    · intro h y hy
      simpa using h y.1 ⟨y, hy, rfl⟩
  have hBQ : ∀ t, t ∈ B ↔ ∀ a ∈ Q, IsIntegral ℤ (star a * β₂ * t) := by
    intro t
    rw [hB, hL]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      simpa using h y hy
    · intro h y hy
      simpa using h y.2 ⟨y, hy, rfl⟩
  have hAle : A ≤ P := fun t ht => ⟨(t, 0), ht, rfl⟩
  have hBle : B ≤ Q := fun t ht => ⟨(0, t), ht, rfl⟩
  set S := Submodule.span (𝓞 E) {t | ∃ x ∈ A, ∃ y ∈ A, t = star x * β₁ * y} with hS
  set T := Submodule.span (𝓞 E) {t | ∃ x ∈ B, ∃ y ∈ B, t = star x * β₂ * y} with hT
  have hS1 : S ≤ LinearMap.range (Algebra.linearMap (𝓞 E) E) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨⟨_, (hAP y).1 hy x (hAle hx)⟩, rfl⟩
  have hT1 : T ≤ LinearMap.range (Algebra.linearMap (𝓞 E) E) := by
    rw [hT, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨⟨_, (hBQ y).1 hy x (hBle hx)⟩, rfl⟩
  have hSc := span_eq_colon P A β₁ h1 h10 hPfg hPne hAP
  have hTc := span_eq_colon Q B β₂ h2 h20 hQfg hQne hBQ
  have hST : S = T := by
    apply le_antisymm
    · intro c hc
      obtain ⟨r, rfl⟩ := hS1 hc
      rw [hTc]
      rintro _ ⟨y, hy, rfl⟩
      have e1 := (hA _).1 ((hSc _).1 hc y.1 ⟨y, hy, rfl⟩)
      have e2 := L.sub_mem (L.smul_mem r hy) e1
      rw [hB]
      convert e2 using 1
      ext <;> simp [Algebra.smul_def]
    · intro c hc
      obtain ⟨r, rfl⟩ := hT1 hc
      rw [hSc]
      rintro _ ⟨y, hy, rfl⟩
      have e1 := (hB _).1 ((hTc _).1 hc y.2 ⟨y, hy, rfl⟩)
      have e2 := L.sub_mem (L.smul_mem r hy) e1
      rw [hA]
      convert e2 using 1
      ext <;> simp [Algebra.smul_def]
  have hmap : S = Submodule.map (Algebra.linearMap (𝓞 E) E) (S.comap (Algebra.linearMap (𝓞 E) E)) :=
    (Submodule.map_comap_eq_self hS1).symm
  refine ⟨A, B, S.comap (Algebra.linearMap (𝓞 E) E),
    isLattice_of A (hPfg.of_le hAle) (dual_ne_bot P A β₁ h1 h10 hPfg hPne hAP),
    isLattice_of B (hQfg.of_le hBle) (dual_ne_bot Q B β₂ h2 h20 hQfg hQne hBQ), hA, hB, hmap,
    hST ▸ hmap, eq_span_fixed P A β₁ h1 h10 hPfg hPne hAP _ hmap⟩

omit [NumberField E] in
theorem herm_star {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (x y : Fin n → E) :
    star (star y ⬝ᵥ (J *ᵥ x)) = star x ⬝ᵥ (J *ᵥ y) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec]

theorem planeSplit : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ u ∈ Λ, u ≠ 0 → ∀ ρ : ℝ, (∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ ρ) → ∃ (γ : GL (Fin 2) E) (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), (γ : Matrix (Fin 2) (Fin 2) E)ᴴ * J * (γ : Matrix (Fin 2) (Fin 2) E) = Matrix.diagonal ![β₁, β₂] ∧ star β₁ = β₁ ∧ star β₂ = β₂ ∧ (∀ φ : E →+* ℂ, 0 < (φ β₁).re ∧ 0 < (φ β₂).re) ∧ Submodule.IsLattice E N₁ ∧ Submodule.IsLattice E N₂ ∧ (∀ t, t ∈ N₁ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![t, 0] ∈ Λ) ∧ (∀ t, t ∈ N₂ ↔ (γ : Matrix (Fin 2) (Fin 2) E) *ᵥ ![0, t] ∈ Λ) ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ N₂, ∃ y ∈ N₂, t = star x * β₂ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 ∧ 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ ρ ^ (2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE J hJ hpos Λ hΛ hdual u hu hu0 ρ hρ
  have hne : ∀ y : Fin 2 → E, y ≠ 0 → star y ⬝ᵥ (J *ᵥ y) ≠ 0 := by
    intro y hy h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hpos φ y hy
    rw [h] at this
    simp at this
  set v := star u ᵥ* J with hv
  let w : Fin 2 → E := ![-v 1, v 0]
  have huw : star u ⬝ᵥ (J *ᵥ w) = 0 := by
    rw [dotProduct_mulVec, ← hv]; simp [w, dotProduct, Fin.sum_univ_two]; ring
  have hwu : star w ⬝ᵥ (J *ᵥ u) = 0 := by rw [← herm_star J hJ, huw, star_zero]
  set β₁ := star u ⬝ᵥ (J *ᵥ u) with hβ₁
  set β₂ := star w ⬝ᵥ (J *ᵥ w) with hβ₂
  have h10 : β₁ ≠ 0 := hne u hu0
  have hb1 : β₁ = v 0 * u 0 + v 1 * u 1 := by
    rw [hβ₁, dotProduct_mulVec, ← hv]; simp [dotProduct, Fin.sum_univ_two]
  have hw0 : w ≠ 0 := by
    intro h
    have a0 := congrFun h 0
    have a1 := congrFun h 1
    simp [w] at a0 a1
    exact h10 (by rw [hb1, a0, a1]; ring)
  have h20 : β₂ ≠ 0 := hne w hw0
  have h1 : star β₁ = β₁ := herm_star J hJ u u
  have h2 : star β₂ = β₂ := herm_star J hJ w w
  let G : Matrix (Fin 2) (Fin 2) E := Matrix.of fun i j => ![u, w] j i
  have hG : G.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [G, w, Matrix.of_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    intro h; apply h10; rw [hb1, ← h]; ring
  have hGv : ∀ a b : E, G *ᵥ ![a, b] = a • u + b • w := by
    intro a b; ext i; simp [G, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hGJ : Gᴴ * J * G = Matrix.diagonal ![β₁, β₂] := by
    have : ∀ i j, (Gᴴ * J * G) i j = star (![u, w] i) ⬝ᵥ (J *ᵥ (![u, w] j)) := by
      intro i j
      simp [G, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_two]; ring
    ext i j
    rw [this]
    fin_cases i <;> fin_cases j
    exacts [rfl, huw, hwu, rfl]
  let f : (E × E) →ₗ[E] (Fin 2 → E) :=
    (LinearMap.toSpanSingleton E _ u).coprod (LinearMap.toSpanSingleton E _ w)
  have hf : ∀ x : E × E, f x = x.1 • u + x.2 • w := fun x => rfl
  have hpair : ∀ x y : E × E, star (f y) ⬝ᵥ (J *ᵥ f x) = star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2 := by
    intro x y
    rw [hf, hf]
    simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, huw, hwu, ← hβ₁, ← hβ₂, smul_eq_mul]
    ring
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have a0 := hpair x (1, 0)
    have a1 := hpair x (0, 1)
    simp [hx, h10, h20] at a0 a1
    exact Prod.ext a0 a1
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  let L : Submodule (𝓞 E) (E × E) := Λ.comap (f.restrictScalars (𝓞 E))
  have hLm : ∀ x, x ∈ L ↔ f x ∈ Λ := fun x => Iff.rfl
  have hLfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (f.restrictScalars (𝓞 E)) hinj
    rw [Submodule.map_comap_eq_of_surjective (f := f.restrictScalars (𝓞 E)) hsurj]
    exact hΛ.fg
  have hu1 : ((1, 0) : E × E) ∈ L := by rw [hLm, hf]; simpa using hu
  have hq : ∃ x ∈ L, x.2 ≠ 0 := by
    by_contra h
    push Not at h
    have : Submodule.span E (Λ : Set (Fin 2 → E)) ≤ (LinearMap.ker (LinearMap.snd E E E)).map f := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, h x hy, rfl⟩
    rw [hΛ.span_eq_top] at this
    obtain ⟨x, hx, hx'⟩ := this (Submodule.mem_top (x := f (0, 1)))
    rw [hinj hx'] at hx
    simp at hx
  have hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (star y.1 * β₁ * x.1 + star y.2 * β₂ * x.2) := by
    intro x
    rw [hLm, hdual]
    constructor
    · intro h y hy
      rw [← hpair, ← mem_range_iff]; exact h _ hy
    · intro h y hy
      obtain ⟨y, rfl⟩ := hsurj y
      rw [mem_range_iff, hpair]; exact h y hy
  obtain ⟨A, B, 𝔫, hA, hB, hA', hB', hS, hT, hfix⟩ :=
    diag_split β₁ β₂ h1 h2 h10 h20 L hLfg ⟨_, hu1, one_ne_zero⟩ hq hL
  have hβn : β₁ ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 := by
    rw [← hS]
    exact Submodule.subset_span ⟨1, (hA' 1).2 hu1, 1, (hA' 1).2 hu1, by simp⟩
  obtain ⟨b, hb, hbβ⟩ := hβn
  have hbβ' : (b : E) = β₁ := hbβ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact h10 (by rw [← hbβ']; rfl)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, β₁, β₂, A, B, 𝔫, hGJ, h1, h2,
    fun φ => ⟨hpos φ u hu0, hpos φ w hw0⟩, hA, hB, fun t => ?_, fun t => ?_, hS, hT, ?_, hfix, ?_⟩
  · rw [hA', hLm, hf]
    change _ ↔ G *ᵥ _ ∈ Λ
    rw [hGv]
  · rw [hB', hLm, hf]
    change _ ↔ G *ᵥ _ ∈ Λ
    rw [hGv]
  · rintro rfl
    exact hb0 hb
  · refine absNorm_le hE.1 𝔫 b hb hb0 ρ fun φ => ?_
    rw [hbβ']
    have him : (φ β₁).im = 0 := by
      have := hE.2.1 φ β₁
      rw [h1] at this
      exact Complex.conj_eq_iff_im.1 this.symm
    rw [← Complex.abs_re_eq_norm.2 him, abs_of_pos (hpos φ u hu0)]
    exact hρ φ

end GlobalTheory.PlaneSplit

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.CharModOne

open scoped nonZeroDivisors

section General

variable {E : Type} [Field E] [NumberField E]

def intMap (σ : E ≃ₐ[ℚ] E) (r : 𝓞 E) : 𝓞 E :=
  ⟨σ r, (RingOfIntegers.isIntegral_coe r).map (σ.toAlgHom.restrictScalars ℤ)⟩

def cj (σ : E ≃ₐ[ℚ] E) (M : Submodule (𝓞 E) E) : Submodule (𝓞 E) E where
  carrier := {x | σ x ∈ M}
  add_mem' {x y} hx hy := by
    show σ (x + y) ∈ M
    rw [map_add]; exact M.add_mem hx hy
  zero_mem' := by
    show σ 0 ∈ M
    rw [map_zero]; exact M.zero_mem
  smul_mem' r x hx := by
    show σ (r • x) ∈ M
    rw [Algebra.smul_def, map_mul]
    have : σ (algebraMap (𝓞 E) E r) * σ x = intMap σ r • σ x := by
      rw [Algebra.smul_def]; rfl
    rw [this]; exact M.smul_mem _ hx

theorem mem_cj (σ : E ≃ₐ[ℚ] E) (M : Submodule (𝓞 E) E) (x : E) : x ∈ cj σ M ↔ σ x ∈ M := Iff.rfl

theorem cj_mono (σ : E ≃ₐ[ℚ] E) {M N : Submodule (𝓞 E) E} (h : M ≤ N) : cj σ M ≤ cj σ N :=
  fun _ hx => h hx

theorem cj_cj (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M : Submodule (𝓞 E) E) : cj σ (cj σ M) = M := by
  ext x; rw [mem_cj, mem_cj, hσ]

theorem cj_mul_le (σ : E ≃ₐ[ℚ] E) (M N : Submodule (𝓞 E) E) : cj σ M * cj σ N ≤ cj σ (M * N) := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  rw [mem_cj, map_mul]
  exact Submodule.mul_mem_mul hx hy

theorem cj_mul (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M N : Submodule (𝓞 E) E) :
    cj σ (M * N) = cj σ M * cj σ N := by
  refine le_antisymm ?_ (cj_mul_le σ M N)
  have h := cj_mono σ (cj_mul_le σ (cj σ M) (cj σ N))
  rwa [cj_cj σ hσ, cj_cj σ hσ, cj_cj σ hσ] at h

theorem one_le_cj_one (σ : E ≃ₐ[ℚ] E) : (1 : Submodule (𝓞 E) E) ≤ cj σ 1 := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨intMap σ y, rfl⟩

theorem cj_one (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) : cj σ (1 : Submodule (𝓞 E) E) = 1 := by
  refine le_antisymm ?_ (one_le_cj_one σ)
  have h := cj_mono σ (one_le_cj_one σ)
  rwa [cj_cj σ hσ] at h

theorem cj_pow (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M : Submodule (𝓞 E) E) (n : ℕ) :
    cj σ (M ^ n) = cj σ M ^ n := by
  induction n with
  | zero => simp [cj_one σ hσ]
  | succ n ih => rw [pow_succ, pow_succ, cj_mul σ hσ, ih]

theorem span_le_cj_span (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (a : E) :
    Submodule.span (𝓞 E) {σ a} ≤ cj σ (Submodule.span (𝓞 E) {a}) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (mem_cj σ _ _).2 (by rw [hσ]; exact Submodule.mem_span_singleton_self a)

theorem cj_span (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (a : E) :
    cj σ (Submodule.span (𝓞 E) {a}) = Submodule.span (𝓞 E) {σ a} := by
  refine le_antisymm ?_ (span_le_cj_span σ hσ a)
  have h := cj_mono σ (span_le_cj_span σ hσ (σ a))
  rwa [cj_cj σ hσ, hσ] at h

theorem span_mul_span_singleton (a b : E) :
    Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {b} = Submodule.span (𝓞 E) {a * b} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem exists_pow_card_eq_span (𝔞 𝔟 : Submodule (𝓞 E) E) (h : 𝔞 * 𝔟 = 1) :
    ∃ a : E, 𝔞 ^ Fintype.card (ClassGroup (𝓞 E)) = Submodule.span (𝓞 E) {a} := by
  have hfa : IsFractional (𝓞 E)⁰ 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (Units.mkOfMulEqOne 𝔞 𝔟 h).isUnit)
  have hfb : IsFractional (𝓞 E)⁰ 𝔟 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (Units.mkOfMulEqOne 𝔟 𝔞 (by rw [mul_comm]; exact h)).isUnit)
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔞, hfa⟩
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔟, hfb⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 := pow_card_eq_one (x := ClassGroup.mk E U)
  rw [← map_pow, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨a, ha⟩ := h1.principal
  refine ⟨a, ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

end General

end GlobalTheory.CharModOne

namespace GlobalTheory.CharModOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem emb_conj (D : D7) (ρ : D.host.E →+* ℂ) (x : D.host.E) :
    ρ (D.host.conj x) = starRingEnd ℂ (ρ x) :=
  D.host.conjE_apply ρ x

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem mod1All_of_isChi : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
    StandardLatticesGL3.Mod1All (χ 𝔞) := by
  intro D χ hχ 𝔞 h𝔞
  set σ := D.host.conj with hσdef
  have hinv : ∀ x, σ (σ x) = x := conj_conj D
  obtain ⟨𝔟, h𝔟, hab⟩ := h𝔞
  have hb : 𝔟 = cj σ 𝔞 := Submodule.ext h𝔟
  have hN1 : ∀ n : ℕ, TaylorLogMetric.N1 D (𝔞 ^ n) := fun n =>
    ⟨𝔟 ^ n, fun x => by rw [hb, ← cj_pow σ hinv]; exact mem_cj σ _ x, by rw [← mul_pow, hab, one_pow]⟩
  have hχpow : ∀ n : ℕ, χ (𝔞 ^ (n + 1)) = χ 𝔞 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ 𝔞 (n + 1), hχ.1 _ _ (hN1 _) ⟨𝔟, h𝔟, hab⟩, ih]; ring
  obtain ⟨a, ha⟩ := exists_pow_card_eq_span 𝔞 𝔟 hab
  set h := Fintype.card (ClassGroup (𝓞 D.host.E)) with hhdef
  have hpos : 0 < h := Fintype.card_pos
  have hb' : 𝔟 ^ h = Submodule.span (𝓞 D.host.E) {σ a} := by rw [hb, ← cj_pow σ hinv, ha, cj_span σ hinv]
  have h1 : Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {σ a} = 1 := by
    rw [← ha, ← hb', ← mul_pow, hab, one_pow]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul] at h1
    have : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [← h1, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hσa0 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  set z : D.host.E := a / σ a with hzdef
  have hσz : σ z = σ a / a := by rw [hzdef, map_div₀, hinv]
  have hz1 : z * σ z = 1 := by rw [hσz, hzdef]; field_simp
  have hz : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, star_eq_conj]
    exact ⟨by rw [mul_comm]; exact hz1, hz1⟩
  have hspan : Submodule.span (𝓞 D.host.E) {z} = 𝔞 ^ (2 * h) := by
    have e1 : z * σ a = a := by rw [hzdef]; field_simp
    calc Submodule.span (𝓞 D.host.E) {z}
        = Submodule.span (𝓞 D.host.E) {z} * (Submodule.span (𝓞 D.host.E) {σ a} * Submodule.span (𝓞 D.host.E) {a}) := by
          rw [mul_comm (Submodule.span (𝓞 D.host.E) {σ a}), h1, mul_one]
      _ = Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {a} := by
          rw [← mul_assoc, span_mul_span_singleton, e1]
      _ = 𝔞 ^ (2 * h) := by rw [← ha, two_mul, pow_add]
  have key : χ 𝔞 ^ (2 * h) = ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ z)⁻¹ := by
    have e := hχ.2 ⟨z, hz⟩
    simp only at e
    rw [hspan] at e
    obtain ⟨k, hk⟩ : ∃ k, 2 * h = k + 1 := ⟨2 * h - 1, by omega⟩
    rw [← e, hk, hχpow]

  have hemb : ∀ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hc : (∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ z)⁻¹) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => inv_mem (hemb τ)
  have hx : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2 * h) (by omega) ?_
    rw [key]
    exact mem_algebraicClosure_iff.1 hc
  refine ⟨hx, fun ρ => ?_⟩
  have hw : (⟨χ 𝔞, hx⟩ : TaylorLogMetric.Qbar) ^ (2 * h) = ∏ τ : D.what₂.Tau, (⟨TaylorLogMetric.embT D τ z, hemb τ⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact key
  have hone : ∀ τ : D.what₂.Tau, ‖ρ ⟨TaylorLogMetric.embT D τ z, hemb τ⟩‖ = 1 := by
    intro τ
    let ρ' : D.host.E →+* ℂ := ρ.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar fun x =>
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom))
    have hρ' : ρ' z = ρ ⟨TaylorLogMetric.embT D τ z, hemb τ⟩ := rfl
    have h2 : ρ' z * starRingEnd ℂ (ρ' z) = 1 := by rw [← emb_conj, ← map_mul, hz1, map_one]
    have h3 : ‖ρ' z‖ ^ 2 = 1 := by
      calc ‖ρ' z‖ ^ 2 = ‖ρ' z * starRingEnd ℂ (ρ' z)‖ := by rw [norm_mul, Complex.norm_conj, sq]
        _ = 1 := by rw [h2, norm_one]
    rw [← hρ']
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  have h4 : ‖ρ ⟨χ 𝔞, hx⟩‖ ^ (2 * h) = 1 := by
    rw [← norm_pow, ← map_pow, hw, map_prod, norm_prod]
    simp [map_inv₀, norm_inv, hone]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h4

end GlobalTheory.CharModOne

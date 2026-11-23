import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.NormOneIdeal

theorem star_integer_smul {E : Type} [Field E] [NumberField E] [StarRing E] (a : 𝓞 E) :
    ∃ b : 𝓞 E, (b : E) = star (a : E) := by
  refine ⟨⟨star (a : E), ?_⟩, rfl⟩
  have h : IsIntegral ℤ (a : E) := a.isIntegral_coe
  exact h.map (starRingEnd E).toIntAlgHom

theorem star_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E]
    {A B C D : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (h2 : ∀ x ∈ B, star x ∈ D) :
    ∀ x ∈ A * B, star x ∈ C * D := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [star_mul']
    exact Submodule.mul_mem_mul (h1 m hm) (h2 n hn)
  · intro a b ha hb
    rw [star_add]
    exact add_mem ha hb

theorem star_mem_span {E : Type} [Field E] [NumberField E] [StarRing E] (z x : E)
    (hx : x ∈ Submodule.span (𝓞 E) {z}) : star x ∈ Submodule.span (𝓞 E) {star z} := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, hb⟩ := star_integer_smul a
  refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  exact congrArg (· * star z) hb

theorem star_mem_pow {E : Type} [Field E] [NumberField E] [StarRing E]
    {A C : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (n : ℕ) :
    ∀ x ∈ A ^ n, star x ∈ C ^ n := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_span] at hx ⊢
    simpa using star_mem_span 1 x hx
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact star_mem_mul ih h1

theorem exists_pow_principal {E : Type} [Field E] [NumberField E]
    (I : (Submodule (𝓞 E) E)ˣ) :
    ∃ (h : ℕ) (z : E), 0 < h ∧ (I : Submodule (𝓞 E) E) ^ h = Submodule.span (𝓞 E) {z} := by
  let e := FractionalIdeal.unitsMulEquivSubmodule (S := nonZeroDivisors (𝓞 E)) (P := E)
  let F := e.symm I
  have hF : ClassGroup.mk E (F ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨z, hz⟩ := ClassGroup.mk_eq_one_iff.1 hF
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), z, Fintype.card_pos, ?_⟩
  rw [← hz]
  have : e (F ^ Fintype.card (ClassGroup (𝓞 E))) = I ^ Fintype.card (ClassGroup (𝓞 E)) := by
    rw [map_pow, MulEquiv.apply_symm_apply]
  rw [← Units.val_pow_eq_pow_val, ← this]
  rfl

theorem pow_eq_span_norm_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (I J : Submodule (𝓞 E) E), (∀ x, x ∈ J ↔ star x ∈ I) → I * J = 1 → (∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n) ∧ ∃ (h : ℕ) (y : E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 E) {y} = I ^ h := by
  intro E _ _ _ I J hJ hIJ
  have h1 : ∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n := by
    intro n x
    refine ⟨star_mem_pow (fun x hx => (hJ x).1 hx) n x, fun hx => ?_⟩
    have := star_mem_pow (A := I) (C := J) (fun x hx => (hJ _).2 (by rwa [star_star])) n _ hx
    rwa [star_star] at this
  refine ⟨h1, ?_⟩
  obtain ⟨h, z, hh, hz⟩ := exists_pow_principal (E := E) ⟨I, J, hIJ, by rw [mul_comm, hIJ]⟩
  change I ^ h = _ at hz
  have hJh : J ^ h = Submodule.span (𝓞 E) {star z} := by
    ext x
    rw [h1, hz]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa using star_mem_span _ _ hx
    · simpa using star_mem_span _ _ hx
  have hm : I ^ h * J ^ h = 1 := by rw [← mul_pow, hIJ, one_pow]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [hz] at hm
    simp only [Submodule.span_zero_singleton, Submodule.bot_mul] at hm
    have : (1 : E) ∈ (⊥ : Submodule (𝓞 E) E) := by
      rw [hm, Submodule.one_eq_span]
      exact Submodule.mem_span_singleton_self _
    simp at this
  have hs0 : star z ≠ 0 := star_ne_zero.2 hz0
  have hinv : Submodule.span (𝓞 E) {(star z)⁻¹} = I ^ h := by
    calc Submodule.span (𝓞 E) {(star z)⁻¹}
        = I ^ h * J ^ h * Submodule.span (𝓞 E) {(star z)⁻¹} := by rw [hm, one_mul]
      _ = I ^ h := by
        rw [mul_assoc, hJh, Submodule.span_mul_span, Set.singleton_mul_singleton,
          mul_inv_cancel₀ hs0, ← Submodule.one_eq_span, mul_one]
  refine ⟨h + h, z * (star z)⁻¹, by omega, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_star]
    field_simp
  · rw [pow_add]
    nth_rewrite 1 [hz]
    rw [← hinv, Submodule.span_mul_span, Set.singleton_mul_singleton]

end GlobalTheory.NormOneIdeal

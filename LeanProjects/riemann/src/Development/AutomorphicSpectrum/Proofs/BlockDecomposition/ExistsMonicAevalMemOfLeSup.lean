import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.Affgl

theorem exists_monic_aeval_mem_of_le_sup {R : Type*} [Ring R] [Algebra ℂ R] (A : Subalgebra ℂ R)
    (V I : Submodule ℂ R) [FiniteDimensional ℂ V] (h : ∀ z ∈ A, z ∈ V ⊔ I) (z : R) (hz : z ∈ A) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ I := by
  have hmemA : ∀ p : Polynomial ℂ, Polynomial.aeval z p ∈ A := by
    intro p
    have e : Polynomial.aeval z p = ((Polynomial.aeval (⟨z, hz⟩ : A) p : A) : R) := by
      simpa using (Polynomial.aeval_algHom_apply A.val (⟨z, hz⟩ : A) p)
    rw [e]
    exact Subtype.property _
  let f : Polynomial ℂ →ₗ[ℂ] R ⧸ I := I.mkQ ∘ₗ (Polynomial.aeval z).toLinearMap
  have hf : ∀ p, f p ∈ V.map I.mkQ := by
    intro p
    obtain ⟨v, hv, i, hi, e⟩ := Submodule.mem_sup.1 (h _ (hmemA p))
    refine ⟨v, hv, ?_⟩
    change I.mkQ v = I.mkQ (Polynomial.aeval z p)
    have hi0 : I.mkQ i = 0 := by simpa using hi
    rw [← e, map_add, hi0, add_zero]
  let g : Polynomial ℂ →ₗ[ℂ] V.map I.mkQ := f.codRestrict _ hf
  have hnot : ¬ Function.Injective g := fun hinj =>
    Polynomial.not_finite (R := ℂ) (Module.Finite.of_injective g hinj)
  obtain ⟨p, hgp, hp⟩ : ∃ p, g p = 0 ∧ p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot ((injective_iff_map_eq_zero g).2 fun p hp => hcon p hp)
  have hI : Polynomial.aeval z p ∈ I := by
    have : f p = 0 := congrArg Subtype.val hgp
    simpa [f] using this
  refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [map_mul, Polynomial.aeval_C, ← Algebra.commutes, ← Algebra.smul_def]
  exact I.smul_mem _ hI

theorem exists_monic_aeval_apply_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (J : Set (Module.End ℂ (Sm E a))) (hJ : Cofin J) (z : Module.End ℂ (Sm E a))
    (hz : z ∈ Zalg E a) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) →
      Polynomial.aeval z p φ = 0 := by
  obtain ⟨-, V, hV, hcov⟩ := hJ
  obtain ⟨p, hp, hI⟩ := exists_monic_aeval_mem_of_le_sup (Zalg E a) V _ hcov z hz
  refine ⟨p, hp, fun φ hφ => ?_⟩
  have key : ∀ y ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, y φ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, j, hj, rfl⟩ := hy
      simp [hφ j hj]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key _ hI

theorem minpoly_on_killed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ z ∈ Zalg E a, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ a J hJ z hz => exists_monic_aeval_apply_eq_zero E a J hJ z hz

end GlobalTheory.CompanionTheory.Affgl

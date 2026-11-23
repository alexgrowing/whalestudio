import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulMem

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

theorem exists_int_mul_integral (x : E) : ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * x) := by
  have h : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  exact ⟨k, hk, by simpa [zsmul_eq_mul] using hi⟩

omit [IsCMField E] in

theorem finite_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (k : ℤ) (hk : k ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ ((k : E) * x) ∧ ∀ τ : Ψ, ‖τ.1 x‖ ≤ R}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (‖(k : ℂ)‖ * R)
  have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
  refine Set.Finite.of_finite_image (f := fun x => (k : E) * x) (hfin.subset ?_)
    (fun x _ y _ h => mul_left_cancel₀ hk' h)
  rintro _ ⟨x, ⟨hi, hb⟩, rfl⟩
  refine ⟨hi, fun φ => ?_⟩
  have : ‖φ x‖ ≤ R := by
    by_cases hφ : φ ∈ Ψ
    · exact hb ⟨φ, hφ⟩
    · have h2 : ComplexEmbedding.conjugate φ ∈ Ψ := by
        by_contra h3
        exact hφ ((hΨ φ).2 h3)
      have := hb ⟨_, h2⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

omit [IsCMField E] in

theorem exists_common_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ v ∈ Λ, ∀ a, IsIntegral ℤ ((k : E) * v a) := by
  classical
  obtain ⟨S, rfl⟩ := hΛ
  choose d hd hdi using (exists_int_mul_integral (E := E))
  refine ⟨∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin r)), d (p.1 p.2),
    Finset.prod_ne_zero_iff.2 fun p _ => hd _, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro a
    have hm : (v, a) ∈ S ×ˢ (Finset.univ : Finset (Fin r)) :=
      Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : (Fin r → E) × Fin r => d (p.1 p.2)) hm
    rw [hc]
    have := (hdi (v a)).mul (isIntegral_algebraMap (R := ℤ) (A := E) (x := c))
    have e : ((d (v a) * c : ℤ) : E) * v a = (d (v a) : E) * v a * algebraMap ℤ E c := by
      simp only [Int.cast_mul, eq_intCast]
      ring
    exact e ▸ this
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro a
    rw [Pi.add_apply, mul_add]
    exact (hx a).add (hy a)
  | smul c x _ hx =>
    intro a
    have := (hx a).mul (RingOfIntegers.isIntegral_coe c)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm, mul_comm]
    exact this

omit [IsCMField E] in

theorem exists_int_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralMultiples.main
  | exact _root_.GlobalTheory.IntegralMultiples.main
  | (apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultiples.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultiples.main ..)

theorem finite_vectors (r : ℕ) (X : Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  refine (Set.Finite.pi' fun _ : Fin r => finite_bounded X.Ψ X.cmType k hk R).subset ?_
  rintro v ⟨hv, hb⟩ a
  exact ⟨hi v hv a, fun τ => hb τ a⟩

theorem finite_automorphisms (r : ℕ) (X : Data E r) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this

theorem latFin : ((∀ (r : ℕ) (X : Data E r) (R : ℝ), {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite) ∧ (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite)) :=
  ⟨finite_vectors, finite_automorphisms⟩

end GlobalTheory.LatFin

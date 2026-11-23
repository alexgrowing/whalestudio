import Mathlib
import GroundTheory.HeightsAndTheta.Theta.UnitaryReduction.UnipotentRadicalPlaces
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

namespace DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate

section NumberFieldFacts

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

open Classical

private theorem filter_mk_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk φ := by rw [mk_embedding, h]
    rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  · rintro (h | h)
    · rw [h, mk_embedding]
    · rw [h, mk_conjugate_eq, mk_embedding]

private theorem embedding_ne_conjugate (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hr : InfinitePlace.IsReal w := InfinitePlace.isReal_iff.mpr
    (ComplexEmbedding.isReal_iff.mpr h.symm)
  exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) hr

theorem sum_re_embedding (t : E) :
    ∑ τ : InfinitePlace E, (τ.embedding t).re = (Algebra.trace ℚ E t : ℝ) / 2 := by
  have h1 : (algebraMap ℚ ℂ (Algebra.trace ℚ E t)) = ∑ σ : E →ₐ[ℚ] ℂ, σ t :=
    trace_eq_sum_embeddings (E := ℂ)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ φ : E →+* ℂ, φ t :=
    (Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ => σ t)).symm
  have h3 : ∑ φ : E →+* ℂ, φ t =
      ∑ w : InfinitePlace E, ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
        φ t :=
    (Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ t)).symm
  have h4 : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ t =
        ((2 * (w.embedding t).re : ℝ) : ℂ) := by
    intro w
    rw [filter_mk_eq, Finset.sum_pair (embedding_ne_conjugate w), ComplexEmbedding.conjugate_coe_eq,
      Complex.add_conj]
  have h5 : ((Algebra.trace ℚ E t : ℝ) : ℂ) =
      ((∑ w : InfinitePlace E, 2 * (w.embedding t).re : ℝ) : ℂ) := by
    rw [show ((Algebra.trace ℚ E t : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E t) by simp,
      h1, h2, h3]
    push_cast
    exact Finset.sum_congr rfl fun w _ => by rw [h4 w]; push_cast; ring
  have h6 := Complex.ofReal_injective h5
  rw [h6, ← Finset.mul_sum]; ring

theorem linearForm_eq_zero_of_integers (Λ : (InfinitePlace E → ℂ) →ₗ[ℝ] ℝ)
    (h : ∀ c : 𝓞 E, Λ (fun τ => τ.embedding (c : E)) = 0) (w : InfinitePlace E → ℂ) :
    Λ w = 0 := by
  classical
  let Ψ : mixedEmbedding.mixedSpace E →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    { toFun := fun p τ => if hτ : InfinitePlace.IsComplex τ then p.2 ⟨τ, hτ⟩ else 0
      map_add' := fun p q => by
        funext τ; by_cases hτ : InfinitePlace.IsComplex τ <;> simp [hτ]
      map_smul' := fun r p => by
        funext τ; by_cases hτ : InfinitePlace.IsComplex τ <;> simp [hτ] }
  have hΨ : ∀ x : E, Ψ (mixedEmbedding E x) = fun τ => τ.embedding x := by
    intro x; funext τ
    have hτ : InfinitePlace.IsComplex τ := IsTotallyComplex.isComplex τ
    simp [Ψ, hτ, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hzero : Λ ∘ₗ Ψ = 0 := by
    refine (mixedEmbedding.latticeBasis E).ext fun i => ?_
    rw [LinearMap.comp_apply, mixedEmbedding.latticeBasis_apply, integralBasis_apply, hΨ,
      LinearMap.zero_apply]
    exact h _
  have hw : Ψ ((0, fun v => w v.1) : mixedEmbedding.mixedSpace E) = w := by
    funext τ
    have hτ : InfinitePlace.IsComplex τ := IsTotallyComplex.isComplex τ
    simp [Ψ, hτ]
  rw [← hw, ← LinearMap.comp_apply, hzero, LinearMap.zero_apply]

end NumberFieldFacts

section DualLattice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem mem_two_invDiff_iff (t : E) :
    t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E ↔
      ∀ c : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((c : E) * t) = 2 * n := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩ c
    rw [invDiff, FractionalIdeal.mem_dual h1] at hy
    obtain ⟨n, hn⟩ := hy (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    have : (c : E) * (2 * y) = (2 : ℚ) • (y * c) := by
      rw [Algebra.smul_def, map_ofNat]; ring
    rw [this, LinearMap.map_smul, ← hn]
    simp
  · intro h
    refine ⟨(2 : E)⁻¹ * t, ?_, by field_simp⟩
    rw [invDiff, FractionalIdeal.mem_dual h1]
    intro a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := h c
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    have : (2 : E)⁻¹ * t * algebraMap (𝓞 E) E c = (2⁻¹ : ℚ) • ((c : E) * t) := by
      rw [Algebra.smul_def]; simp only [map_inv₀, map_ofNat]; ring
    rw [this, LinearMap.map_smul, hn]
    simp

theorem exists_of_integral_pairing (z : InfinitePlace E → ℂ)
    (hz : ∀ c : 𝓞 E, ∃ n : ℤ, ∑ τ : InfinitePlace E, (τ.embedding (c : E) * z τ).re = n) :
    ∃ t : E, (∀ τ, z τ = τ.embedding t) ∧
      t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E := by
  classical
  let b := integralBasis E
  choose n hn using fun i => hz (RingOfIntegers.basis E i)
  have hB := traceForm_nondegenerate ℚ E
  let db := (Algebra.traceForm ℚ E).dualBasis hB b
  let t : E := ∑ i, ((2 * n i : ℤ) : ℚ) • db i
  let L1 : E →ₗ[ℚ] ℝ :=
    { toFun := fun e => ((Algebra.trace ℚ E (e * t) : ℚ) : ℝ) / 2
      map_add' := fun x y => by rw [add_mul, map_add, Rat.cast_add, add_div]
      map_smul' := fun q x => by
        rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, Rat.cast_mul, RingHom.id_apply,
          Rat.smul_def]
        ring }
  let L2 : E →ₗ[ℚ] ℝ :=
    { toFun := fun e => ∑ τ : InfinitePlace E, (τ.embedding e * z τ).re
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by rw [map_add, add_mul, Complex.add_re]
      map_smul' := fun q x => by
        simp only [RingHom.id_apply, Rat.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [map_mul, map_ratCast, mul_assoc,
          show ((q : ℂ)) = ((q : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul] }
  have hbt : ∀ j, Algebra.trace ℚ E (b j * t) = 2 * n j := by
    intro j
    simp only [t, Finset.mul_sum, mul_smul_comm, map_sum, LinearMap.map_smul, smul_eq_mul]
    have : ∀ i, Algebra.trace ℚ E (b j * db i) = if j = i then 1 else 0 := by
      intro i
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left hB b i j
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    push_cast; ring
  have hL : L1 = L2 := by
    refine b.ext fun j => ?_
    change ((Algebra.trace ℚ E (b j * t) : ℚ) : ℝ) / 2 = ∑ τ : InfinitePlace E, (τ.embedding (b j) * z τ).re
    rw [hbt j, integralBasis_apply]
    have := hn j
    simp only [RingOfIntegers.coe_eq_algebraMap] at this ⊢
    rw [this]; push_cast; ring
  have hL' : ∀ e : E, ((Algebra.trace ℚ E (e * t) : ℚ) : ℝ) / 2 =
      ∑ τ : InfinitePlace E, (τ.embedding e * z τ).re := fun e => LinearMap.congr_fun hL e
  let d : InfinitePlace E → ℂ := fun τ => z τ - τ.embedding t
  let Λ : (InfinitePlace E → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ τ : InfinitePlace E, (w τ * d τ).re
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_mul, Complex.add_re]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by
          rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul] }
  have hΛ : ∀ c : 𝓞 E, Λ (fun τ => τ.embedding (c : E)) = 0 := by
    intro c
    change ∑ τ : InfinitePlace E, (τ.embedding (c : E) * d τ).re = 0
    have e1 : ∀ τ : InfinitePlace E, (τ.embedding (c : E) * d τ).re =
        (τ.embedding (c : E) * z τ).re - (τ.embedding ((c : E) * t)).re := by
      intro τ; simp only [d, mul_sub, Complex.sub_re, map_mul]
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_sub_distrib, ← hL', sum_re_embedding]
    ring
  have hd : ∀ τ, d τ = 0 := by
    have h0 := linearForm_eq_zero_of_integers Λ hΛ (fun τ => conj (d τ))
    change ∑ τ : InfinitePlace E, (conj (d τ) * d τ).re = 0 at h0
    have hnn : ∀ τ ∈ Finset.univ, 0 ≤ (conj (d τ) * d τ).re := fun τ _ => by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]; exact Complex.normSq_nonneg _
    intro τ
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 τ (Finset.mem_univ τ)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at this
    exact Complex.normSq_eq_zero.mp this
  refine ⟨t, fun τ => sub_eq_zero.mp (hd τ), (mem_two_invDiff_iff t).mpr fun c => ?_⟩
  obtain ⟨m, hm⟩ := hz c
  refine ⟨m, ?_⟩
  have := hL' (c : E)
  rw [hm] at this
  exact_mod_cast (by linarith : ((Algebra.trace ℚ E ((c : E) * t) : ℚ) : ℝ) = 2 * m)

end DualLattice

section DualBasis

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_extend_of_submodule (A : Submodule (𝓞 E) V) (s : A →ₗ[𝓞 E] 𝓞 E) :
    ∃ σ : V →ₗ[E] E, ∀ x : A, σ (x : V) = ((s x : 𝓞 E) : E) := by
  classical
  obtain ⟨bs, hbA, _hspan, hli⟩ := exists_linearIndependent E (A : Set V)
  let bb := Basis.span hli
  let σ₀ := bb.constr E (fun i : bs => ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E))
  obtain ⟨σ, hσ⟩ := LinearMap.exists_extend σ₀
  have hrange : Set.range ((↑) : bs → V) = bs := Subtype.range_coe
  have hσb : ∀ i : bs, σ (i : V) = ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E) := by
    intro i
    have hi : (i : V) ∈ Submodule.span E (Set.range ((↑) : bs → V)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 : σ (i : V) = σ₀ ⟨i, hi⟩ := by
      rw [← hσ]; rfl
    have h2 : (⟨i, hi⟩ : Submodule.span E (Set.range ((↑) : bs → V))) = bb i := by
      ext; rw [Basis.span_apply]
    rw [h1, h2, Basis.constr_basis]

  have hP : ∀ y ∈ Submodule.span (𝓞 E) (bs : Set V), ∀ hy : y ∈ A,
      σ y = ((s ⟨y, hy⟩ : 𝓞 E) : E) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hxA; exact hσb ⟨x, hx⟩
    | zero => intro h0; simp [show (⟨0, h0⟩ : A) = 0 from rfl]
    | add x y hx hy ihx ihy =>
      intro hxyA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have hyA : y ∈ A := Submodule.span_le.mpr hbA hy
      rw [map_add, ihx hxA, ihy hyA, show (⟨x + y, hxyA⟩ : A) = ⟨x, hxA⟩ + ⟨y, hyA⟩ from rfl,
        map_add]
      push_cast; rfl
    | smul c x hx ihx =>
      intro hcxA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have e1 : σ (c • x) = (c : E) * σ x := by
        rw [← algebraMap_smul E c x, LinearMap.map_smul, smul_eq_mul,
          RingOfIntegers.coe_eq_algebraMap]
      have e2 : s ⟨c • x, hcxA⟩ = c * s ⟨x, hxA⟩ := by
        rw [show (⟨c • x, hcxA⟩ : A) = c • ⟨x, hxA⟩ from rfl, LinearMap.map_smul, smul_eq_mul]
      rw [e1, e2, ihx hxA]
      simp
  refine ⟨σ, fun x => ?_⟩
  have hx : (x : V) ∈ Submodule.span E (bs : Set V) := by
    rw [_hspan]; exact Submodule.subset_span x.2
  obtain ⟨m, c, v, hv, hxv⟩ : ∃ (m : ℕ) (c : Fin m → E) (v : Fin m → V), (∀ i, v i ∈ bs) ∧
      (x : V) = ∑ i, c i • v i := by
    obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').mp hx
    exact ⟨m, c, fun i => (g i : V), fun i => (g i).2, hg.symm⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ c
  choose o ho using fun i => hd i (Finset.mem_univ i)
  have hdx : ((d : 𝓞 E) : E) • (x : V) = ∑ i, o i • v i := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (o i) (v i), ho i, Algebra.smul_def, mul_smul,
      RingOfIntegers.coe_eq_algebraMap]
  have hyP : ∑ i, o i • v i ∈ Submodule.span (𝓞 E) (bs : Set V) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv i))
  have hyA : ∑ i, o i • v i ∈ A := Submodule.span_le.mpr hbA hyP
  have key := hP _ hyP hyA
  have hyeq : (⟨∑ i, o i • v i, hyA⟩ : A) = (d : 𝓞 E) • x := by
    apply Subtype.ext
    change (∑ i, o i • v i) = (d : 𝓞 E) • (x : V)
    rw [← hdx, ← algebraMap_smul E (d : 𝓞 E) (x : V), RingOfIntegers.coe_eq_algebraMap]
  rw [hyeq, map_smul, smul_eq_mul, ← hdx, map_smul, smul_eq_mul] at key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d (by exact_mod_cast h)
  push_cast at key
  exact mul_left_cancel₀ hd0 key

end DualBasis

section DualBasis2

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_dualBasis (A : Submodule (𝓞 E) V) (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → V) (σ : Fin n → (V →ₗ[E] E)),
      (∀ i, a i ∈ A) ∧ (∀ i, ∀ x ∈ A, σ i x ∈ Set.range (algebraMap (𝓞 E) E)) ∧
      ∀ x ∈ espan A, x = ∑ i, σ i x • a i := by
  classical
  have : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.mpr hA
  have : Module.Flat (𝓞 E) A := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have h1 : ((a : 𝓞 E) : E) • (x : V) = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
      exact congrArg Subtype.val ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (by exact_mod_cast h)
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left ha0)
  have : Module.FinitePresentation (𝓞 E) A := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) A := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) A
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose σ hσ using fun i : Fin n => exists_extend_of_submodule A ((LinearMap.proj i).comp h)
  have hxA : ∀ x : A, (x : V) = ∑ i, σ i x • (f (Pi.single i 1) : V) := by
    intro x
    have h1 : x = f (h x) := (LinearMap.congr_fun hh x).symm
    have h2 : h x = ∑ i, h x i • (Pi.single i 1 : Fin n → 𝓞 E) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul, hσ i x, ← algebraMap_smul E (h x i),
      RingOfIntegers.coe_eq_algebraMap]
    rfl
  refine ⟨n, fun i => (f (Pi.single i 1) : V), σ, fun i => (f (Pi.single i 1)).2, ?_, ?_⟩
  · intro i x hx
    exact ⟨h ⟨x, hx⟩ i, by rw [hσ i ⟨x, hx⟩, RingOfIntegers.coe_eq_algebraMap]; rfl⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hxA ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz =>
      conv_lhs => rw [hy, hz]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
    | smul c y _ hy =>
      conv_lhs => rw [hy]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end DualBasis2

section Fibres

variable {E : Type} [Field E] [NumberField E]

variable (S : MetSpace E) (τ : InfinitePlace E)

theorem pt_add' (x y : S.V) : S.pt τ (x + y) = S.pt τ x + S.pt τ y := TensorProduct.tmul_add _ _ _

theorem pt_zero' : S.pt τ 0 = 0 := TensorProduct.tmul_zero _ _

theorem pt_smul' (e : E) (x : S.V) : S.pt τ (e • x) = τ.embedding e • S.pt τ x := by
  change (1 : CAt τ.embedding) ⊗ₜ[E] (e • x) = τ.embedding e • ((1 : CAt τ.embedding) ⊗ₜ[E] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', CAt.smul_def, CAt.complex_smul_def]

theorem pt_sum_smul' {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → S.V) :
    S.pt τ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, τ.embedding (c i) • S.pt τ (v i) := by
  change (1 : CAt τ.embedding) ⊗ₜ[E] (∑ i ∈ s, c i • v i) = _
  rw [TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl fun i _ => pt_smul' S τ (c i) (v i)

theorem tmul_eq_smul_pt (z : CAt τ.embedding) (v : S.V) :
    (z ⊗ₜ[E] v : S.FibSp τ) = (CAt.ofComplex τ.embedding).symm z • S.pt τ v := by
  change z ⊗ₜ[E] v = (CAt.ofComplex τ.embedding).symm z • ((1 : CAt τ.embedding) ⊗ₜ[E] v)
  rw [TensorProduct.smul_tmul', CAt.complex_smul_def, AlgEquiv.apply_symm_apply, mul_one]

theorem fibSub_eq_span (W : Submodule E S.V) :
    S.fibSub W τ = Submodule.span ℂ (S.pt τ '' (W : Set S.V)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z w =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      have hmem : S.pt τ (w : S.V) ∈ Submodule.span ℂ (S.pt τ '' (W : Set S.V)) :=
        Submodule.subset_span ⟨w, w.2, rfl⟩
      have h2 := (Submodule.span ℂ (S.pt τ '' (W : Set S.V))).smul_mem
        ((CAt.ofComplex τ.embedding).symm z) hmem
      rw [← tmul_eq_smul_pt] at h2
      exact h2
    | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(1 : CAt τ.embedding) ⊗ₜ[E] (⟨w, hw⟩ : W), by
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]; rfl⟩

theorem pt_mem_span_of_mem_espan (A : Submodule (𝓞 E) S.V) {w : S.V} (hw : w ∈ espan A) :
    S.pt τ w ∈ Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [pt_zero']; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [pt_add']; exact Submodule.add_mem _ hx hy
  | smul e x _ hx => rw [pt_smul']; exact Submodule.smul_mem _ _ hx

theorem fibSub_espan_eq_span (A : Submodule (𝓞 E) S.V) :
    S.fibSub (espan A) τ = Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by
  rw [fibSub_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨w, hw, rfl⟩; exact pt_mem_span_of_mem_espan S τ A hw
  · exact Submodule.span_mono (Set.image_mono (fun x hx => Submodule.subset_span hx))

theorem mem_span_pt (y : S.FibSp τ) : y ∈ Submodule.span ℂ (Set.range (S.pt τ)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul z v =>
    rw [tmul_eq_smul_pt]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add y y' hy hy' => exact Submodule.add_mem _ hy hy'

theorem ext_pt {M : Type} [AddCommGroup M] [Module ℂ M] {X Y : S.FibSp τ →ₗ[ℂ] M}
    (h : ∀ v, X (S.pt τ v) = Y (S.pt τ v)) : X = Y := by
  ext y
  induction mem_span_pt S τ y using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact h v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

theorem fibMap_pt' (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (v : S.V) :
    S.fibMap T φ τ (S.pt τ v) = T.pt τ (φ v) := rfl

theorem fibMap_mem_fibSub (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (W : Submodule E T.V)
    (hφ : ∀ v, φ v ∈ W) (y : S.FibSp τ) : S.fibMap T φ τ y ∈ T.fibSub W τ := by
  rw [fibSub_eq_span]
  induction mem_span_pt S τ y using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [fibMap_pt']; exact Submodule.subset_span ⟨φ v, hφ v, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

def fibFun (σ : S.V →ₗ[E] E) : S.FibSp τ →ₗ[ℂ] ℂ :=
  (S.dualFunctional τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) : S.FibSp τ →L[ℂ] ℂ)

theorem fibFun_pt (σ : S.V →ₗ[E] E) (v : S.V) :
    fibFun S τ σ (S.pt τ v) = τ.embedding (σ v) := by
  change (CAt.ofComplex τ.embedding).symm
    (S.dualCoord τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) ((1 : CAt τ.embedding) ⊗ₜ[E] v)) = _
  rw [dualCoord_tmul_tmul, one_mul, mul_one, CAt.algebraMap_apply, AlgEquiv.symm_apply_apply]

theorem dualBasis_at (A : Submodule (𝓞 E) S.V) {n : ℕ} (a : Fin n → S.V) (σ : Fin n → (S.V →ₗ[E] E))
    (hid : ∀ x ∈ espan A, x = ∑ i, σ i x • a i) {x : S.FibSp τ}
    (hx : x ∈ S.fibSub (espan A) τ) :
    x = ∑ i, fibFun S τ (σ i) x • S.pt τ (a i) := by
  rw [fibSub_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    conv_lhs => rw [hid w hw, pt_sum_smul']
    exact Finset.sum_congr rfl fun i _ => by rw [fibFun_pt]
  | zero => simp
  | add y z _ _ hy hz =>
    conv_lhs => rw [hy, hz]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
  | smul c y _ hy =>
    conv_lhs => rw [hy]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end Fibres

section Adjoints

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

theorem trace_adjoint' (T : H₁ →ₗ[ℂ] H₁) :
    LinearMap.trace ℂ H₁ (LinearMap.adjoint T) = conj (LinearMap.trace ℂ H₁ T) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.adjoint_inner_right, inner_conj_symm]

theorem re_trace_comp_adjoint (X Y : H₁ →ₗ[ℂ] H₂) :
    (LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y)).re =
      (LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X)).re := by
  have e1 : LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y) =
      LinearMap.trace ℂ H₁ (LinearMap.adjoint Y ∘ₗ X) := by
    rw [LinearMap.trace_comp_comm']
  have e2 : LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X) =
      LinearMap.trace ℂ H₁ (LinearMap.adjoint X ∘ₗ Y) := by
    rw [LinearMap.trace_comp_comm']
  have e3 : LinearMap.adjoint (LinearMap.adjoint Y ∘ₗ X) = LinearMap.adjoint X ∘ₗ Y := by
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  rw [e1, e2, ← e3, trace_adjoint', Complex.conj_re]

theorem adjoint_maps (X : H₁ →ₗ[ℂ] H₂) (K₁ : Submodule ℂ H₁) (K₂ : Submodule ℂ H₂)
    (h1 : ∀ y ∈ K₁ᗮ, X y = 0) (h2 : ∀ y, X y ∈ K₂) :
    (∀ y ∈ K₂ᗮ, LinearMap.adjoint X y = 0) ∧ ∀ y, LinearMap.adjoint X y ∈ K₁ := by
  constructor
  · intro y hy
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (h2 u) hy
  · intro y
    rw [← Submodule.orthogonal_orthogonal K₁, Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.adjoint_inner_right, h1 u hu, inner_zero_left]

end Adjoints

section IdealMaps

variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

theorem map_smulIdeal_mem (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V)
    (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V') (hU : ∀ a ∈ A, U a ∈ B) {x : V}
    (hx : x ∈ smulIdeal aa A) : U x ∈ smulIdeal aa B := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, rfl⟩ := hy
    rw [LinearMap.map_smul]
    exact Submodule.subset_span ⟨c, hc, U a, hU a ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hy

theorem form_mem_of_smulIdeal (aa : FractionalIdeal (𝓞 E)⁰ E) (B : Submodule (𝓞 E) V)
    (ρ : V →ₗ[E] E) (hρ : ∀ b ∈ B, ρ b ∈ Set.range (algebraMap (𝓞 E) E)) {x : V}
    (hx : x ∈ smulIdeal aa B) : ρ x ∈ (aa : Submodule (𝓞 E) E) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, b, hb, rfl⟩ := hy
    obtain ⟨o, ho⟩ := hρ b hb
    rw [LinearMap.map_smul, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o hc
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hy

theorem mem_espan_of_smulIdeal (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ smulIdeal aa A) : x ∈ espan A := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, _, a, ha, rfl⟩ := hy
    exact Submodule.smul_mem _ c (Submodule.subset_span ha)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [← algebraMap_smul E c y]; exact Submodule.smul_mem _ _ hy

theorem map_espan_mem (A : Submodule (𝓞 E) V) (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V')
    (hU : ∀ a ∈ A, U a ∈ espan B) {x : V} (hx : x ∈ espan A) : U x ∈ espan B := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hU y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hy

end IdealMaps

section FibMaps

variable {E : Type} [Field E] [NumberField E]

theorem fibMap_fibSub (S T : MetSpace E) (τ : InfinitePlace E) (φ : S.V →ₗ[E] T.V)
    (W : Submodule E S.V) (W' : Submodule E T.V) (hφ : ∀ w ∈ W, φ w ∈ W') {y : S.FibSp τ}
    (hy : y ∈ S.fibSub W τ) : S.fibMap T φ τ y ∈ T.fibSub W' τ := by
  rw [fibSub_eq_span] at hy ⊢
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [fibMap_pt']; exact Submodule.subset_span ⟨φ v, hφ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem eqOn_fibSub (S : MetSpace E) (τ : InfinitePlace E) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : Submodule (𝓞 E) S.V) {X Y : S.FibSp τ →ₗ[ℂ] M}
    (h : ∀ a ∈ A, X (S.pt τ a) = Y (S.pt τ a)) {x : S.FibSp τ}
    (hx : x ∈ S.fibSub (espan A) τ) : X x = Y x := by
  rw [fibSub_espan_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, ha, rfl⟩ := hy; exact h a ha
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, map_smul, hy]

theorem pt_mem_fibSub (S : MetSpace E) (τ : InfinitePlace E) (W : Submodule E S.V) {w : S.V}
    (hw : w ∈ W) : S.pt τ w ∈ S.fibSub W τ := by
  rw [fibSub_eq_span]; exact Submodule.subset_span ⟨w, hw, rfl⟩

end FibMaps

end DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors

theorem dualHom (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] :
    DualHom.Statement F E := by
  intro S S' A B' hA hB'
  obtain ⟨nb, b, ρ, hbB, hρO, hidB⟩ := exists_dualBasis B' hB'
  ext T
  constructor
  · rintro ⟨hTS, hTZ⟩
    obtain ⟨na, a, σ, haA, hσO, hidA⟩ := exists_dualBasis A hA
    have hwB : ∀ τ, ∀ y ∈ (S'.fibSub (espan B') τ)ᗮ, LinearMap.adjoint (T τ) y = 0 :=
      fun τ => (adjoint_maps (T τ) _ _ (hTS τ).1 (hTS τ).2).1
    have hwA : ∀ τ y, LinearMap.adjoint (T τ) y ∈ S.fibSub (espan A) τ :=
      fun τ => (adjoint_maps (T τ) _ _ (hTS τ).1 (hTS τ).2).2
    have hint : ∀ (i : Fin na) (j : Fin nb) (c : 𝓞 E), ∃ n : ℤ, ∑ τ : InfinitePlace E,
        (τ.embedding (c : E) *
          (fun τ : InfinitePlace E => fibFun S τ (σ i) (LinearMap.adjoint (T τ) (S'.pt τ (b j)))) τ).re
          = n := by
      intro i j c
      let U' : S.V →ₗ[E] S'.V := ((c : E) • σ i).smulRight (b j)
      have hU'v : ∀ v, U' v = ((c : E) * σ i v) • b j := fun v => by
        simp only [U', LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]
      let γ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ := fun τ =>
        S.fibMap S' U' τ ∘ₗ ((S.fibSub (espan A) τ).starProjection : S.FibSp τ →ₗ[ℂ] S.FibSp τ)
      have hγ : γ ∈ homImage A B' := by
        refine ⟨fun τ => ⟨fun y hy => ?_, fun y => ?_⟩, U', fun x hx => ?_, fun τ x hx => ?_⟩
        · simp only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            (Submodule.starProjection_apply_eq_zero_iff _).mpr hy, map_zero]
        · exact fibMap_mem_fibSub S τ S' U' (espan B') (fun v => by
            rw [hU'v]; exact Submodule.smul_mem _ _ (Submodule.subset_span (hbB j))) _
        · obtain ⟨o, ho⟩ := hσO i x hx
          rw [hU'v, ← ho, RingOfIntegers.coe_eq_algebraMap, ← map_mul, algebraMap_smul]
          exact Submodule.smul_mem _ _ (hbB j)
        · have hpt := pt_mem_fibSub S τ (espan A) (Submodule.subset_span hx : x ∈ espan A)
          simp only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.starProjection_eq_self_iff.mpr hpt]
          rfl
      obtain ⟨n, hn⟩ := hTZ γ hγ
      refine ⟨n, ?_⟩
      rw [← hn]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have hU' : S.fibMap S' U' τ =
          ((τ.embedding (c : E)) • fibFun S τ (σ i)).smulRight (S'.pt τ (b j)) := by
        refine ext_pt S τ fun v => ?_
        rw [fibMap_pt', hU'v, pt_smul', LinearMap.smulRight_apply, LinearMap.smul_apply, fibFun_pt,
          map_mul, smul_eq_mul]
      have hcomp : γ τ ∘ₗ LinearMap.adjoint (T τ) =
          ((τ.embedding (c : E)) • (fibFun S τ (σ i) ∘ₗ LinearMap.adjoint (T τ))).smulRight
            (S'.pt τ (b j)) := by
        refine LinearMap.ext fun y => ?_
        have hy := hwA τ y
        simp only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Submodule.starProjection_eq_self_iff.mpr hy, hU', LinearMap.smulRight_apply,
          LinearMap.smul_apply]
      change (τ.embedding (c : E) * fibFun S τ (σ i) (LinearMap.adjoint (T τ) (S'.pt τ (b j)))).re =
        hsInner S (T τ) (γ τ)
      unfold hsInner
      rw [re_trace_comp_adjoint (T τ) (γ τ), hcomp, LinearMap.trace_smulRight,
        LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    choose t ht using fun i j => exists_of_integral_pairing _ (hint i j)
    let U : S'.V →ₗ[E] S.V := ∑ j, (ρ j).smulRight (∑ i, t i j • a i)
    have hUv : ∀ v, U v = ∑ j, ρ j v • ∑ i, t i j • a i := fun v => by
      simp only [U, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine ⟨U, fun y hy => ?_, fun τ => ?_⟩
    · rw [hUv]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_smul]
      refine Submodule.subset_span ⟨ρ j y * t i j, ?_, a i, haA i, rfl⟩
      obtain ⟨o, ho⟩ := hρO j y hy
      rw [← ho, ← Algebra.smul_def]
      exact Submodule.smul_mem (_ : Submodule (𝓞 E) E) o (ht i j).2
    · have hUfib : S'.fibMap S U τ =
          ∑ j, (fibFun S' τ (ρ j)).smulRight (S.pt τ (∑ i, t i j • a i)) := by
        refine ext_pt S' τ fun v => ?_
        rw [fibMap_pt', hUv, pt_sum_smul', LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.smulRight_apply, fibFun_pt]
      have hwU : LinearMap.adjoint (T τ) = S'.fibMap S U τ ∘ₗ
          ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ) := by
        refine LinearMap.ext fun y => ?_
        have hperp := (S'.fibSub (espan B') τ).sub_starProjection_mem_orthogonal y
        have hPB := (S'.fibSub (espan B') τ).starProjection_apply_mem y
        have hsplit : y = (S'.fibSub (espan B') τ).starProjection y +
            (y - (S'.fibSub (espan B') τ).starProjection y) := by abel
        rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        conv_lhs => rw [hsplit, map_add, hwB τ _ hperp, add_zero]
        generalize (S'.fibSub (espan B') τ).starProjection y = x at hPB ⊢
        have hx := dualBasis_at S' τ B' b ρ hidB hPB
        conv_lhs => rw [hx]
        rw [map_sum, hUfib, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smulRight_apply]
        congr 1
        have hA' := dualBasis_at S τ A a σ hidA (hwA τ (S'.pt τ (b j)))
        rw [hA', pt_sum_smul']
        exact Finset.sum_congr rfl fun i _ => by rw [(ht i j).1 τ]
      rw [← hwU, LinearMap.adjoint_adjoint]
  · rintro ⟨U, hU, hT⟩
    have hUE : ∀ y ∈ espan B', U y ∈ espan A := fun y hy =>
      map_espan_mem B' A U (fun x hx => mem_espan_of_smulIdeal _ A (hU x hx)) hy
    have hX : ∀ τ, (∀ y ∈ (S'.fibSub (espan B') τ)ᗮ, (S'.fibMap S U τ ∘ₗ
        ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) y = 0) ∧
        ∀ y, (S'.fibMap S U τ ∘ₗ
          ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) y ∈
            S.fibSub (espan A) τ := by
      intro τ
      refine ⟨fun y hy => ?_, fun y => ?_⟩
      · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          (Submodule.starProjection_apply_eq_zero_iff _).mpr hy, map_zero]
      · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact fibMap_fibSub S' S τ U (espan B') (espan A) hUE
          ((S'.fibSub (espan B') τ).starProjection_apply_mem y)
    refine ⟨fun τ => ?_, fun γ hγ => ?_⟩
    · rw [hT τ]
      exact adjoint_maps _ _ _ (hX τ).1 (hX τ).2
    · obtain ⟨_, U', hU'A, hγpt⟩ := hγ
      let t : E := ∑ j, ρ j (U' (U (b j)))
      have ht : t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E := by
        refine Submodule.sum_mem (_ : Submodule (𝓞 E) E) fun j _ => ?_
        exact form_mem_of_smulIdeal _ B' (ρ j) (hρO j)
          (map_smulIdeal_mem _ A B' U' hU'A (hU (b j) (hbB j)))
      obtain ⟨n, hn⟩ := (mem_two_invDiff_iff t).mp ht 1
      refine ⟨n, ?_⟩
      have hU'E : ∀ y ∈ espan A, U' y ∈ espan B' := fun y hy =>
        map_espan_mem A B' U' (fun x hx => Submodule.subset_span (hU'A x hx)) hy
      have hτ : ∀ τ : InfinitePlace E, hsInner S (T τ) (γ τ) = (τ.embedding t).re := by
        intro τ
        unfold hsInner
        rw [re_trace_comp_adjoint, hT τ, LinearMap.adjoint_adjoint]
        have hγU : ∀ x ∈ S.fibSub (espan A) τ, γ τ x = S.fibMap S' U' τ x := fun x hx =>
          eqOn_fibSub S τ A (fun a ha => by rw [hγpt τ a ha, fibMap_pt']) hx
        have hcomp : γ τ ∘ₗ (S'.fibMap S U τ ∘ₗ
            ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) =
            ∑ j, ((fibFun S' τ (ρ j)) ∘ₗ
              ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)).smulRight
                (S'.pt τ (U' (U (b j)))) := by
          refine LinearMap.ext fun y => ?_
          simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.sum_apply,
            LinearMap.smulRight_apply]
          have hPB := (S'.fibSub (espan B') τ).starProjection_apply_mem y
          generalize (S'.fibSub (espan B') τ).starProjection y = x at hPB ⊢
          have hx := dualBasis_at S' τ B' b ρ hidB hPB
          conv_lhs => rw [hx]
          rw [map_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, map_smul, fibMap_pt',
            hγU _ (pt_mem_fibSub S τ (espan A) (hUE _ (Submodule.subset_span (hbB j)))),
            fibMap_pt']
        have hterm : ∀ j, LinearMap.trace ℂ (S'.FibSp τ) (((fibFun S' τ (ρ j)) ∘ₗ
            ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)).smulRight
              (S'.pt τ (U' (U (b j))))) = τ.embedding (ρ j (U' (U (b j)))) := by
          intro j
          rw [LinearMap.trace_smulRight, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.starProjection_eq_self_iff.mpr (pt_mem_fibSub S' τ (espan B')
              (hU'E _ (hUE _ (Submodule.subset_span (hbB j))))), fibFun_pt]
        rw [hcomp, map_sum, Finset.sum_congr rfl fun j _ => hterm j, ← map_sum]
      unfold eucl
      rw [Finset.sum_congr rfl fun τ _ => hτ τ, sum_re_embedding]
      have hn' : Algebra.trace ℚ E t = 2 * n := by simpa using hn
      rw [hn']
      push_cast
      ring

end UnitaryReduction

end GroundTheory.Heights₂.Theta

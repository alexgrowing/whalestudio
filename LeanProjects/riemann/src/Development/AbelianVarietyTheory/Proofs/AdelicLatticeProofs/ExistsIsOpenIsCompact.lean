import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

open NumberField IsDedekindDomain MeasureTheory Polynomial

namespace GlobalTheory.GLIntegral

section general

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def glSub (S : Subring A) : Subgroup (GL ι A) where
  carrier := {g | (∀ i j, (g : Matrix ι ι A) i j ∈ S) ∧ ∀ i j, ((g⁻¹ : GL ι A) : Matrix ι ι A) i j ∈ S}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix ι ι A) i j ∈ S := fun i j => by
      rw [Matrix.one_apply]; split_ifs
      exacts [S.one_mem, S.zero_mem]
    exact ⟨h, by simpa using h⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact S.sum_mem fun k _ => S.mul_mem (ha _ _) (hb _ _)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact S.sum_mem fun k _ => S.mul_mem (hb' _ _) (ha' _ _)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

variable [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem isOpen_glSub (S : Subring A) (hS : IsOpen (S : Set A)) :
    IsOpen (glSub (ι := ι) S : Set (GL ι A)) := by
  have h : IsOpen {m : Matrix ι ι A | ∀ i j, m i j ∈ S} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hS.preimage (continuous_id.matrix_elem i j)
  exact (h.preimage Units.continuous_val).inter (h.preimage Units.continuous_coe_inv)

theorem isCompact_glSub [T2Space A] (S : Subring A) (hS : IsCompact (S : Set A)) :
    IsCompact (glSub (ι := ι) S : Set (GL ι A)) := by
  have h : IsCompact {m : Matrix ι ι A | ∀ i j, m i j ∈ S} := by
    have := isCompact_univ_pi fun _ : ι => isCompact_univ_pi fun _ : ι => hS
    have e : {m : Matrix ι ι A | ∀ i j, m i j ∈ S} =
        Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => (S : Set A) :=
      Set.ext fun m => ⟨fun hm i _ j _ => hm i j, fun hm i j => hm i trivial j trivial⟩
    rw [e]; exact this
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix ι ι A)).isCompact_preimage
    (h.prod (h.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  constructor
  · rintro ⟨h1, h1'⟩
    exact ⟨h1, _, h1', rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL ι A) : Matrix ι ι A) := MulOpposite.op_injective hm'
    rw [← this]; exact hm

end general

def intSubring (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ U : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  refine ⟨glSub (intSubring F), isOpen_glSub _ ?_,
    isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral F)⟩
  exact RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

end GlobalTheory.GLIntegral

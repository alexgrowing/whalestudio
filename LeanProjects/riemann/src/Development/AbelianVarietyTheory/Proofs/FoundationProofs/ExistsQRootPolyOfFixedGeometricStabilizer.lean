import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

open Polynomial IntermediateField

namespace GlobalTheory.K5.Span

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

variable (p Ω) in

def baseField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x})

theorem algebraMap_mem_baseField (a : O0 p) : algebraMap (O0 p) Ω a ∈ baseField p Ω :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem ggeo_fix_baseField {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) {x : Ω} (hx : x ∈ baseField p Ω) :
    g x = x := by
  have hle : baseField p Ω ≤ RingHom.eqLocusField (g : Ω →+* Ω) (RingHom.id Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro z (⟨a, rfl⟩ | hz)
    · show g (algebraMap (O0 p) Ω a) = algebraMap (O0 p) Ω a
      exact g.commutes a
    · show g z = z
      exact hg z hz
  exact hle hx

noncomputable def toGal (σ : Ω ≃ₐ[baseField p Ω] Ω) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun a =>
    σ.commutes (⟨algebraMap (O0 p) Ω a, algebraMap_mem_baseField a⟩ : baseField p Ω)

theorem toGal_apply (σ : Ω ≃ₐ[baseField p Ω] Ω) (x : Ω) : toGal σ x = σ x := rfl

theorem isAlgebraic_baseField (h : IsClo p Ω) : Algebra.IsAlgebraic (baseField p Ω) Ω := by
  haveI := h.alg
  refine ⟨fun x => ?_⟩
  obtain ⟨P, hP0, hPx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x
  let φ : O0 p →+* baseField p Ω :=
    (algebraMap (O0 p) Ω).codRestrict (baseField p Ω) algebraMap_mem_baseField
  have hφ : Function.Injective φ := fun a b hab => h.inj (congrArg Subtype.val hab)
  refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP0, ?_⟩
  rw [aeval_def, eval₂_map]
  have : (algebraMap (baseField p Ω) Ω).comp φ = algebraMap (O0 p) Ω := by
    ext a; rfl
  rw [this, ← aeval_def, hPx]

end GlobalTheory.K5.Span

open GlobalTheory.K5 GlobalTheory.K5.Span in

theorem GlobalTheory.K5.span_fixed_ggeo_stab : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ h T N y hy
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  haveI := h.clo
  set L := baseField p Ω
  haveI : CharZero L := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := isAlgebraic_baseField h
  haveI : IsAlgClosure L Ω := ⟨h.clo, inferInstance⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  set M : IntermediateField L Ω := IntermediateField.adjoin L {T.qq N}
  have hyM : y ∈ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, mem_fixedField_iff]
    intro σ hσ
    have hq : σ (T.qq N) = T.qq N :=
      (mem_fixingSubgroup_iff M σ).1 hσ _ (mem_adjoin_simple_self L _)
    refine hy (toGal σ) (Subgroup.mem_inf.2 ⟨fun x hx => ?_, ?_⟩)
    · exact σ.commutes (⟨x, Subfield.subset_closure (Or.inr hx)⟩ : L)
    · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, toGal_apply, hq]
  have hyA : y ∈ (aeval (T.qq N) : L[X] →ₐ[L] Ω).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval,
      ← adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)]
    exact hyM
  obtain ⟨P, hP⟩ := hyA
  set q0 : L := ⟨algebraMap (O0 p) Ω (qO p), algebraMap_mem_baseField _⟩
  set Q : L[X] := X ^ (p ^ N) - C q0
  have hpN : p ^ N ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hQm : Q.Monic := monic_X_pow_sub_C _ hpN
  have hQd : Q.natDegree = p ^ N := natDegree_X_pow_sub_C
  have hQ1 : Q ≠ 1 := by
    intro e; rw [e, natDegree_one] at hQd; exact hpN hQd.symm
  have hQq : aeval (T.qq N) Q = 0 := by
    simp only [Q, map_sub, map_pow, aeval_X, aeval_C, Basic.qq_pow]
    exact sub_self _
  set R := P %ₘ Q
  have hRd : R.natDegree < p ^ N := hQd ▸ natDegree_modByMonic_lt P hQm hQ1
  have hR : aeval (T.qq N) R = y := by
    have e := congrArg (aeval (T.qq N)) (modByMonic_add_div P Q)
    rw [map_add, map_mul, hQq, zero_mul, add_zero] at e
    rw [e]; exact hP
  refine ⟨fun j => ((R.coeff j : L) : Ω), fun j g hg => ggeo_fix_baseField hg (R.coeff j).2, ?_⟩
  rw [← hR, aeval_eq_sum_range' hRd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def]
  rfl

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem fits_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K)
    (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ →
    Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  intro E _ _ _ w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep h₁ h₂
  obtain ⟨ha₁, hr₁, hd₁, hs₁⟩ := h₁
  obtain ⟨ha₂, hr₂, hd₂, hs₂⟩ := h₂
  have hne : Q₁ * Q₂ ≠ 0 := hsep.ne_zero
  have hQ₁ : Q₁ ≠ 0 := left_ne_zero_of_mul hne
  have hQ₂ : Q₂ ≠ 0 := right_ne_zero_of_mul hne
  have hcop : IsCoprime (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) :=
    hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
  have hfst : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).1 = aeval u₁ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  have hsnd : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).2 = aeval u₂ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Algebra.adjoin K.E {((u₁, u₂) : B₁.A × B₂.A)} = ⊤
    obtain ⟨a, b, hab⟩ := hcop
    have e₁ : aeval u₁ b * aeval u₁ (Q₂.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₁) hab
      rw [map_add, map_mul, map_mul, hr₁, mul_zero, zero_add, map_one] at this
      exact this
    have e₂ : aeval u₂ a * aeval u₂ (Q₁.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₂) hab
      rw [map_add, map_mul, map_mul, hr₂, mul_zero, add_zero, map_one] at this
      exact this
    rw [eq_top_iff]
    rintro ⟨y, z⟩ -
    have hy : y ∈ (aeval u₁ : K.E[X] →ₐ[K.E] B₁.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₁]; trivial
    have hz : z ∈ (aeval u₂ : K.E[X] →ₐ[K.E] B₂.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₂]; trivial
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have key : ((aeval u₁ p, aeval u₂ r) : B₁.A × B₂.A) =
        aeval ((u₁, u₂) : B₁.A × B₂.A) (b * Q₂.map e.symm.toRingHom * p + a * Q₁.map e.symm.toRingHom * r) := by
      refine Prod.ext ?_ ?_
      · rw [hfst, map_add, map_mul, map_mul, map_mul, map_mul, hr₁, mul_zero, zero_mul, add_zero, e₁, one_mul]
      · rw [hsnd, map_add, map_mul, map_mul, map_mul, map_mul, hr₂, mul_zero, zero_mul, zero_add, e₂, one_mul]
    exact key ▸ Polynomial.aeval_mem_adjoin_singleton K.E _
  · show aeval ((u₁, u₂) : B₁.A × B₂.A) ((Q₁ * Q₂).map e.symm.toRingHom) = 0
    rw [Polynomial.map_mul]
    refine Prod.ext ?_ ?_
    · rw [hfst, map_mul, hr₁, zero_mul]; rfl
    · rw [hsnd, map_mul, hr₂, mul_zero]; rfl
  · show Module.finrank K.E (B₁.A × B₂.A) = (Q₁ * Q₂).natDegree
    rw [Module.finrank_prod, hd₁, hd₂, natDegree_mul hQ₁ hQ₂]
  · exact Prod.ext hs₁ hs₂

end GlobalTheory.KapLat

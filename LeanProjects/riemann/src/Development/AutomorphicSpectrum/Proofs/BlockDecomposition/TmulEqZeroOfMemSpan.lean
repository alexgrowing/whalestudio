import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.TensCompl

theorem tmul_eq_zero_of_mem_span {R N A : Type} [CommRing R] [AddCommGroup N] [Module R N]
    [CommRing A] [Algebra R A] (c : R) (M : ℕ) (hN : ∀ x : N, c ^ M • x = 0) (n : N) (a : A)
    (ha : a ∈ Ideal.span {algebraMap R A c ^ M}) : n ⊗ₜ[R] a = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have : b * algebraMap R A c ^ M = c ^ M • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this, ← smul_tmul, hN, zero_tmul]

theorem main : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ r M N _ _ B _ _ T _ _ g h1 h2 h3
  constructor
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul n y =>
      obtain ⟨x, hx⟩ := h2 y
      refine ⟨n ⊗ₜ x, ?_⟩
      have h0 := tmul_eq_zero_of_mem_span (r 0) M h1 n _ hx
      rw [tmul_sub, sub_eq_zero] at h0
      rw [h0]
      simp
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
  · intro w hw k
    choose s hs using h2
    let I : Ideal T := Ideal.span {algebraMap R T (r 0) ^ M}
    let P : Submodule R B := (Ideal.span {algebraMap R B (r 0) ^ M}).restrictScalars R
    have key : ∀ x : B, g x ∈ I → r k • x ∈ P := fun x hx => h3 x hx k
    have hadd : ∀ y y' : T, r k • s (y + y') - (r k • s y + r k • s y') ∈ P := by
      intro y y'
      rw [← smul_add, ← smul_sub]
      apply key
      have e : g (s (y + y') - (s y + s y')) =
          (y - g (s y)) + (y' - g (s y')) - (y + y' - g (s (y + y'))) := by
        simp only [map_sub, map_add]; ring
      rw [e]
      exact I.sub_mem (I.add_mem (hs y) (hs y')) (hs _)
    have hsmul : ∀ (c : R) (y : T), r k • s (c • y) - c • (r k • s y) ∈ P := by
      intro c y
      rw [smul_comm c, ← smul_sub]
      apply key
      have e : g (s (c • y) - c • s y) =
          algebraMap R T c * (y - g (s y)) - (c • y - g (s (c • y))) := by
        rw [map_sub, map_smul, mul_sub, ← Algebra.smul_def, ← Algebra.smul_def]; abel
      rw [e]
      exact I.sub_mem (I.mul_mem_left _ (hs y)) (hs _)
    let L : T →ₗ[R] B ⧸ P :=
      { toFun := fun y => P.mkQ (r k • s y)
        map_add' := fun y y' => by
          rw [← map_add]
          exact (Submodule.Quotient.eq P).mpr (hadd y y')
        map_smul' := fun c y => by
          simp only [RingHom.id_apply]
          rw [← map_smul]
          exact (Submodule.Quotient.eq P).mpr (hsmul c y) }
    let F : (B ⧸ P) →ₗ[R] N →ₗ[R] N ⊗[R] B :=
      P.liftQ (TensorProduct.mk R N B).flip (by
        intro b hb
        rw [LinearMap.mem_ker]
        ext n
        exact tmul_eq_zero_of_mem_span (r 0) M h1 n b hb)
    let Φ : N ⊗[R] T →ₗ[R] N ⊗[R] B := TensorProduct.lift (F ∘ₗ L).flip
    have hΦ : ∀ (n : N) (y : T), Φ (n ⊗ₜ y) = n ⊗ₜ (r k • s y) := fun n y => by
      simp [Φ, F, L]
    have hcomp : ∀ v : N ⊗[R] B, Φ (g.toLinearMap.lTensor N v) = r k • v := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul n b =>
        rw [LinearMap.lTensor_tmul, hΦ, ← tmul_smul, ← sub_eq_zero, ← tmul_sub, ← smul_sub]
        apply tmul_eq_zero_of_mem_span (r 0) M h1 n
        apply key
        have e : g (s (g b) - b) = -(g b - g (s (g b))) := by
          simp only [map_sub]; ring
        have e' : (g.toLinearMap) b = g b := rfl
        rw [e', e]
        exact I.neg_mem (hs _)
      | add a b ha hb => rw [map_add, map_add, ha, hb, smul_add]
    rw [← hcomp w, hw, map_zero]

end GlobalTheory.CompanionTheory.TensCompl

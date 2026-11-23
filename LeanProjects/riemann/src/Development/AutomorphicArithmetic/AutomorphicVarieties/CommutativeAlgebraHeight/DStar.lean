import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DExtPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnopMemCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_star :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (σ : E →ₐ[A] Eᵐᵒᵖ) (M : Submonoid E), Submodule.span A (M : Set E) = ⊤ → (∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i (σ x).unop = D.lam i x) → D.op.pull σ = D ∧ (∀ x ∈ D.CH, (σ x).unop ∈ D.CH) ∧ (Function.Surjective σ → ∀ x ∈ D.ker, (σ x).unop ∈ D.ker) := by
  intro n A E _ _ _ D σ M hM h
  obtain ⟨o1, o2, o3⟩ := UpperTheory.V.CA.d_op D
  obtain ⟨p1, -, p3, p4⟩ := UpperTheory.V.CA.d_pull D.op σ
  have key : D.op.pull σ = D := by
    refine UpperTheory.V.CA.d_ext _ _ M hM fun x hx i h1 h2 => ?_
    rw [← h x hx i h1 h2]
    unfold Det.lam
    rw [p1 x, ← o1, MulOpposite.op_unop]
  refine ⟨key, fun x hx => ?_, fun hs x hx => ?_⟩
  · rw [← o3, MulOpposite.op_unop]
    exact p3 x (by rw [key]; exact hx)
  · rw [← o2, MulOpposite.op_unop]
    exact (p4 hs).1 x (by rw [key]; exact hx)

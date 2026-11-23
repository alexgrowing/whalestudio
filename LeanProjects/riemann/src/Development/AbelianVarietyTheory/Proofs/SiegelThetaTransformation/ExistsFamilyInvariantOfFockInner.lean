import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyExistsMulIsLowerTriangular

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem sum_mul_conj_orthonormalBasis {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Fintype ι] (b b' : OrthonormalBasis ι ℂ V) (l l' : V →ₗ[ℂ] ℂ) :
    ∑ j, l (b j) * conj (l' (b j)) = ∑ j, l (b' j) * conj (l' (b' j)) := by
  have := FiniteDimensional.complete ℂ V
  have h (l : V →ₗ[ℂ] ℂ) : ∃ a : V, ∀ v, l v = inner ℂ a v :=
    ⟨(InnerProductSpace.toDual ℂ V).symm (LinearMap.toContinuousLinearMap l), fun v => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨a, ha⟩ := h l
  obtain ⟨a', ha'⟩ := h l'
  simp only [ha, ha', inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner]

theorem exists_family_invariant_of_fockInner {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (hW : W ≠ ⊥) :
    ∃ (m : ℕ) (P : Fin m → MvPolynomial σ ℂ), (∀ j, P j ∈ W) ∧ (∃ j, P j ≠ 0) ∧
      ∀ f : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ Q ∈ W, f Q ∈ W) →
        (∀ Q Q', MvPoly.fockInner (f Q) (f Q') = MvPoly.fockInner Q Q') →
        ∀ l l' : MvPolynomial σ ℂ →ₗ[ℂ] ℂ,
          ∑ j, l (f (P j)) * conj (l' (f (P j))) = ∑ j, l (P j) * conj (l' (P j)) := by
  let cr : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => MvPoly.fockInner (y : MvPolynomial σ ℂ) x
      conj_inner_symm := fun x y => MvPoly.fockInner_conj_symm _ _
      re_inner_nonneg := fun x => by
        rw [MvPoly.fockInner_self, RCLike.ofReal_re]; exact MvPoly.fockNormSq_nonneg _
      add_left := fun x y z => MvPoly.fockInner_add_right _ _ _
      smul_left := fun x y r => MvPoly.fockInner_smul_right _ _ _
      definite := fun x hx => by
        rw [MvPoly.fockInner_self] at hx
        exact Subtype.ext (MvPoly.fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp hx)) }
  letI : NormedAddCommGroup W := cr.toNormedAddCommGroup
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore cr.toCore
  let b := stdOrthonormalBasis ℂ W
  have hpos : 0 < Module.finrank ℂ W := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]; exact hW
  refine ⟨_, fun j => b j, fun j => (b j).2, ⟨⟨0, hpos⟩, fun e => ?_⟩, fun f hf hi l l' => ?_⟩
  · exact b.orthonormal.ne_zero _ (Subtype.ext e)
  · let U : W →ₗᵢ[ℂ] W := (f.restrict hf).isometryOfInner fun x y => hi _ _
    exact sum_mul_conj_orthonormalBasis (b.map (U.toLinearIsometryEquiv rfl)) b
      (l ∘ₗ W.subtype) (l' ∘ₗ W.subtype)

theorem exists_invFam_rowHighest : ∀ (T : Type) [Fintype T] [DecidableEq T] (p q n : ℕ)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ), p + q ≤ n →
    ∃ (m : ℕ) (P : Fin m → Harm.Poly ℂ T p q (Fin n)), (∀ j, P j ∈ Harm.rowHighest ℂ c c') ∧
      (∃ j, P j ≠ 0) ∧ InvFam P := by
  intro T _ _ p q n c c' h
  obtain ⟨m, P, h₁, h₂, h₃⟩ := exists_family_invariant_of_fockInner
    (Harm.rowHighest (κ := Fin n) ℂ c c') (Harm.rowHighest_ne_bot h c c')
  refine ⟨m, P, h₁, h₂, fun u hu z w => ?_⟩
  have hs : star u * u = 1 := funext fun t => Units.ext (Matrix.mem_unitaryGroup_iff'.mp (hu t))
  refine h₃ (Harm.colActHom u).toLinearMap (fun Q hQ => Harm.colAct_mem_rowHighest u hQ)
    (fun Q Q' => ?_) (MvPolynomial.aeval z).toLinearMap (MvPolynomial.aeval w).toLinearMap
  change MvPoly.fockInner (Harm.colAct ℂ T p q (Fin n) u Q) (Harm.colAct ℂ T p q (Fin n) u Q') = _
  rw [Harm.fockInner_colAct, ← AlgEquiv.mul_apply, ← map_mul, hs, map_one, AlgEquiv.one_apply]

end GlobalTheory.SW

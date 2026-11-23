import Mathlib

namespace GlobalTheory.EmbeddingMean

theorem card_fibre {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] [DecidableEq (A →ₐ[K] C)]
    (f : A →ₐ[K] C) :
    (Finset.univ.filter (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B) = f)).card
      = Module.finrank A B := by
  letI : Algebra A C := f.toRingHom.toAlgebra
  haveI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [← AlgHom.card A B C, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun g => { g.1.toRingHom with
        commutes' := fun a => by
          have := DFunLike.congr_fun g.2 a
          exact this }
      invFun := fun h => ⟨h.restrictScalars K, AlgHom.ext fun a => h.commutes a⟩
      left_inv := fun g => Subtype.ext (AlgHom.ext fun _ => rfl)
      right_inv := fun h => AlgHom.ext fun _ => rfl }

theorem tower {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] :
    (∀ f : A →ₐ[K] C, ∃ g : B →ₐ[K] C, g.comp (IsScalarTower.toAlgHom K A B) = f) ∧
    ∀ F : (A →ₐ[K] C) → ℝ,
      (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B))) / (Module.finrank K B : ℝ)
        = (∑ f : A →ₐ[K] C, F f) / (Module.finrank K A : ℝ) := by
  classical
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  have hpos : 0 < Module.finrank A B := Module.finrank_pos
  refine ⟨fun f => ?_, fun F => ?_⟩
  · have h := card_fibre (B := B) f
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (h ▸ hpos)
    exact ⟨g, (Finset.mem_filter.mp hg).2⟩
  · have hsum : (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B)))
        = (Module.finrank A B : ℝ) * ∑ f : A →ₐ[K] C, F f := by
      rw [← Finset.sum_fiberwise Finset.univ
        (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => F f)
        (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
        Finset.sum_const, nsmul_eq_mul]
      congr 2
      convert card_fibre (B := B) f
    have hA : (Module.finrank K A : ℝ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := K) (M := A)).ne'
    have hB : (Module.finrank A B : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [hsum, ← Module.finrank_mul_finrank K A B]
    push_cast
    field_simp

end GlobalTheory.EmbeddingMean

import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

open GlobalTheory.CompanionTheory.Ar.FlagBun

def IsGenFam (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) : Prop :=
  (∀ s a, u s a a = 1) ∧ (∀ s a b, a < b → u s a b = 0) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) = ⊤

def revInv {G : Type} [Field G] {r : ℕ} (u : Matrix (Fin r) (Fin r) G) : Matrix (Fin r) (Fin r) G :=
  (u.transpose⁻¹).submatrix Fin.rev Fin.rev

theorem genU_isGenFam (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : IsGenFam Ω (GenField Ω r) (genU Ω r) := by
  have hdiag : ∀ s (a : Fin (r s)), genU Ω r s a a = 1 := fun s a => by
    simp [genU]
  have habove : ∀ s (a b : Fin (r s)), a < b → genU Ω r s a b = 0 := fun s a b h => by
    simp [genU, not_lt.2 h.le, h.ne]
  have hbelow : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
      genU Ω r q.1 q.2.1.1 q.2.1.2 =
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) :=
    fun q => by
      simp only [genU]
      exact dif_pos q.2.2
  refine ⟨hdiag, habove, ?_, ?_⟩
  · have hinj : Function.Injective
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) := by
      rw [IsScalarTower.coe_toAlgHom']
      exact IsFractionRing.injective _ _
    have hX := (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map' hinj
    have hfun : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) ∘ MvPolynomial.X := by
      funext q
      exact hbelow q
    rw [hfun]
    exact hX
  · rw [eq_top_iff]
    intro x _
    have hXmem : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro q
      rw [← hbelow q]
      exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1⟩, rfl⟩
    have hA : ∀ a : MvPolynomial (GenIx r) Ω,
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) a ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro a
      induction a using MvPolynomial.induction_on
      · rename_i c
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ c
      · rename_i p q hp hq
        rw [map_add]
        exact add_mem hp hq
      · rename_i p i hp
        rw [map_mul]
        exact mul_mem hp (hXmem i)
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) x
    exact div_mem (hA a) (hA b)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

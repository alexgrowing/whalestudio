import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
open Matrix
open GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.GenFam

variable {G : Type} [Field G] {S : Type} {r : S → ℕ}

theorem adjoin_low (F : Type) [Field F] [Algebra F G] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G)
    (h1 : ∀ s a, u s a a = 1) (h0 : ∀ s a b, a < b → u s a b = 0) :
    IntermediateField.adjoin F (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin F
        (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, a, b⟩, rfl⟩
    show u s a b ∈ IntermediateField.adjoin F _
    rcases lt_trichotomy a b with h | h | h
    · rw [h0 s a b h]; exact zero_mem _
    · rw [h, h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (a, b), h⟩, rfl⟩
  · rintro _ ⟨⟨s, ⟨a, b⟩, h⟩, rfl⟩
    exact ⟨⟨s, a, b⟩, rfl⟩

variable {Ω : Type} [Field Ω] [Algebra Ω G]

theorem of_gen [Finite S] {u v : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G} (hu : IsGenFam Ω G u)
    (h1 : ∀ s a, v s a a = 1) (h0 : ∀ s a b, a < b → v s a b = 0)
    (h : ∀ s a b, u s a b ∈
      IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2)) :
    IsGenFam Ω G v := by
  have htop : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2) = ⊤ := by
    rw [eq_top_iff, ← hu.2.2.2]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    exact h _ _ _
  refine ⟨h1, h0, ?_, htop⟩
  rw [adjoin_low Ω v h1 h0] at htop
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range
      fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) G := by
    refine IntermediateField.isAlgebraic_adjoin_iff_top.1 ⟨fun x => ?_⟩
    exact isAlgebraic_algebraMap (⟨x, by rw [htop]; trivial⟩ : IntermediateField.adjoin Ω _)
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω _ hu.2.2.1.cardinalMk_le_trdeg).1

theorem inv_mem {n : ℕ} (F : IntermediateField Ω G) (M : Matrix (Fin n) (Fin n) G) (hd : IsUnit M.det)
    (h : ∀ a b, M a b ∈ F) (a b : Fin n) : M⁻¹ a b ∈ F := by
  let M' : Matrix (Fin n) (Fin n) F := fun a b => ⟨M a b, h a b⟩
  have e : M = M'.map (algebraMap F G) := rfl
  have hd' : IsUnit M'.det := by
    rw [isUnit_iff_ne_zero] at hd ⊢
    intro h0
    apply hd
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have : M⁻¹ = (M'⁻¹).map (algebraMap F G) := by
    apply Matrix.inv_eq_right_inv
    rw [e, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd', Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact (M'⁻¹ a b).2

end PositivityTheory.Xgp.GenFam

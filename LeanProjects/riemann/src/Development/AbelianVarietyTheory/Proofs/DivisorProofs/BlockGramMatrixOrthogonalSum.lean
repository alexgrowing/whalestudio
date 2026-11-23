import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory

theorem symp_plane_block : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α : Type} [Fintype α] [DecidableEq α] {d₁ : ℕ} (JA : Matrix α α S) (J₁ : Matrix (Fin d₁) (Fin d₁) S)
    (G : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) S),
    (∀ a a', G (Fin.castAdd 2 a) (Fin.castAdd 2 a') = J₁ a a') → (∀ a t, G (Fin.castAdd 2 a) (Fin.natAdd d₁ t) = 0) →
    (∀ t a, G (Fin.natAdd d₁ t) (Fin.castAdd 2 a) = 0) → G (Fin.natAdd d₁ 0) (Fin.natAdd d₁ 0) = 0 →
    G (Fin.natAdd d₁ 1) (Fin.natAdd d₁ 1) = 0 → G (Fin.natAdd d₁ 0) (Fin.natAdd d₁ 1) = 1 →
    G (Fin.natAdd d₁ 1) (Fin.natAdd d₁ 0) = -1 → ∀ Y Y' : Matrix α (Fin (d₁ + 2)) S,
    symp c ξ JA G Y Y' = symp c ξ JA J₁ (Matrix.of fun i a => Y i (Fin.castAdd 2 a)) (Matrix.of fun i a => Y' i (Fin.castAdd 2 a)) +
      Algebra.trace R S (ξ * ∑ i, ∑ k, Y i (Fin.natAdd d₁ 0) * JA i k * c (Y' k (Fin.natAdd d₁ 1))) -
      Algebra.trace R S (ξ * ∑ i, ∑ k, Y i (Fin.natAdd d₁ 1) * JA i k * c (Y' k (Fin.natAdd d₁ 0))) := by
  intro R S _ _ _ c ξ α _ _ d₁ JA J₁ G h11 h12 h21 h00 h11' h01 h10 Y Y'
  unfold symp
  rw [← map_add, ← map_sub, ← mul_add, ← mul_sub]
  congr 2
  unfold hTens
  simp only [Fin.sum_univ_add, Fin.sum_univ_two, h11, h12, h21, h00, h11', h01, h10, Matrix.of_apply,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    map_neg, Finset.sum_const_zero]
  ring

end GlobalTheory

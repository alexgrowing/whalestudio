import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem det_mul_eq_sum_mnr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R) :
    (L * M).det = ∑ g : Fin n → ι, (∏ i, L i (g i)) * mnr M g := by
  have h1 : (L * M).det =
      (Matrix.detRowAlternating (R := R) (n := Fin n)).toMultilinearMap
        (fun i => ∑ j, L i j • M j) := by
    have : (L * M) = Matrix.of (fun i => ∑ j, L i j • M j) := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    rfl
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem exists_mnr_ne_zero_of_left_inverse :
    ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
      (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
      L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  intro R _ _ ι _ _ n M L h
  by_contra hc
  push_neg at hc
  have key := det_mul_eq_sum_mnr M L
  rw [h, Matrix.det_one] at key
  simp [hc] at key

end GlobalTheory.CompanionTheory.GodementH

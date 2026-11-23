import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.SDBound

variable {D : D7}

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_mul_isIntegral_fin {n : ℕ} (z : Fin n → Fin n → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l k, IsIntegral ℤ ((d : D.host.E) * z l k) := by
  classical
  choose c hc hi using fun p : Fin n × Fin n => exists_nat_mul_isIntegral (z p.1 p.2)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l k => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ (l, k)), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi (l, k))
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem finPart_incA_mem {o : D.host.E} (ho : IsIntegral ℤ o) : finPart D (incA D o) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩

theorem hermAt_single (S : HSp D) (y : Fin S.rank → AE D) (k : Fin S.rank) (a : AE D) :
    hermAt S y (Pi.single k a) = cA D a * (gA S *ᵥ y) k := by
  unfold hermAt
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, RingHom.map_zero]
    simp only [zero_mul, Finset.sum_const_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem exists_mul_mem_intAt : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v) := by
  intro D S v Λ ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  obtain ⟨d, hd, hint⟩ := exists_nat_mul_isIntegral_fin (fun l k => (S.gram)⁻¹ l k)
  refine ⟨d * m, Nat.mul_pos hd hm, fun y hy l => ⟨Ideal.mul_mem_left _ _ (hsupp y hy l), ?_⟩⟩
  have key : ∀ k, finPart D ((m : AE D) * (gA S *ᵥ y) k) ∈ intAE D := fun k => by
    have hx : (m : AE D) • (Pi.single k ε : Fin S.rank → AE D) ∈ Λ := by
      refine hmul _ fun i => ?_
      by_cases hi : i = k
      · rw [hi, Pi.single_eq_same]; exact hε
      · rw [Pi.single_eq_of_ne hi]; exact ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
    have h1 := (((hdual y (hsupp y hy)).1 hy) _ hx).2
    rwa [← Pi.single_smul', smul_eq_mul, hermAt_single, RingHom.map_mul (cA D), map_natCast, hc, mul_assoc,
      hact _ (mulVec_mem_idAt _ (hsupp y hy) k)] at h1
  have e1 : y l = ∑ k, incA D ((S.gram)⁻¹ l k) * (gA S *ᵥ y) k := by
    have : giA S *ᵥ (gA S *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, giA_mul_gA, Matrix.one_mulVec]
    exact (congrFun this l).symm
  have e2 : ((d * m : ℕ) : AE D) * y l =
      ∑ k, incA D ((d : D.host.E) * (S.gram)⁻¹ l k) * ((m : AE D) * (gA S *ᵥ y) k) := by
    rw [e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e2, map_sum]
  refine sum_mem fun k _ => ?_
  rw [RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (finPart_incA_mem (hint l k)) (key k)

end GlobalTheory.IwaPlace.SDBound

end

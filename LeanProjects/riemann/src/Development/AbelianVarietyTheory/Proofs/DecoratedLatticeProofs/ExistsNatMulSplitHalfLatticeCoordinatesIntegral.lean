import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (x : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * x ∈ 𝒪[k] := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have h2 : b ∣ ((Q ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Units.mul_left_dvd, Nat.cast_pow]
    exact pow_dvd_pow_of_dvd hQ m
  obtain ⟨d, hd⟩ := h2
  refine ⟨Q ^ m, pow_pos Fintype.card_pos m, ?_⟩
  have hb1 : (algebraMap 𝒪[k] k b) ≠ 0 := fun h => hb0 (Subtype.ext h)
  have h3 : ((Q ^ m : ℕ) : k) = algebraMap 𝒪[k] k b * algebraMap 𝒪[k] k d := by
    rw [← map_mul, ← hd, map_natCast]
  have h4 : ((Q ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) = ((d * a : 𝒪[k]) : k) := by
    rw [h3]
    change _ = algebraMap 𝒪[k] k (d * a)
    rw [map_mul]
    field_simp
  rw [h4]
  exact (d * a).2

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (f : ι → k) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * f i ∈ 𝒪[k] := by
  classical
  choose n hn hf using fun i => exists_nat_mul_mem (f i)
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (n i : k), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hf i)

end GlobalTheory.FinPl.RdBound

open GlobalTheory.FinPl.RdBound in

theorem GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := exists_nat_mul_mem_family (fun x : n × Fin T.rank => β.b' x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := exists_nat_mul_mem_family (fun x : Fin S.rank × n' => α.b x.1 x.2)
  refine ⟨K₁ * M * K₂, Nat.mul_pos (Nat.mul_pos hK₁ hM) hK₂, fun u hu hh i j => ?_⟩
  have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
  have hint : ∀ a b, (M : k) * p.pr (u a b) ∈ 𝒪[k] := fun a b => by
    rw [p.int_iff]
    have h1 : p.sec ((M : k) * p.pr (u a b)) = (M : AE D) * u a b := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, p.sec_pr, hh a b]
    rw [h1]
    refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
    rw [RingHom.map_mul, map_natCast]
    exact hden _ hu' a b
  change (_ : k) * (β.b' * Matrix.map u p.pr * α.b) i j ∈ 𝒪[k]
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine sum_mem fun a _ => ?_
  have e : ((K₁ * M * K₂ : ℕ) : k) * (β.b' i a * Matrix.map u p.pr a b * α.b b j) =
      ((K₁ : k) * β.b' i a) * ((M : k) * p.pr (u a b)) * ((K₂ : k) * α.b b j) := by
    rw [Matrix.map_apply]; push_cast; ring
  rw [e]
  exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))

end

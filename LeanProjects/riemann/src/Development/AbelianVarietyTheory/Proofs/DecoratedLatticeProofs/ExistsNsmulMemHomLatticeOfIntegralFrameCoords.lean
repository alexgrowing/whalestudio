import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (c : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * c ∈ 𝒪[k] := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[k]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : b ∣ ((Nat.card 𝓀[k] ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[k] ^ m, pow_pos Nat.card_pos m, ?_⟩
  have hb' : (algebraMap 𝒪[k] k b) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0
  have : ((Nat.card 𝓀[k] ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) =
      algebraMap 𝒪[k] k (d * a) := by
    rw [← map_natCast (algebraMap 𝒪[k] k), hd, map_mul, map_mul]
    field_simp
  rw [this]
  exact (d * a).2

theorem exists_nat_mul_mem_fin {ι : Type} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * c i ∈ 𝒪[k] := by
  classical
  choose N hN h using fun i => exists_nat_mul_mem (c i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_mem {n n' m m' : Type} [Fintype n] [Fintype n'] {N : ℕ} (b : Matrix m n k) (b' : Matrix n' m' k)
    (hb : ∀ i a, (N : k) * b i a ∈ 𝒪[k]) (hb' : ∀ a j, (N : k) * b' a j ∈ 𝒪[k]) (x : Matrix n n' k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) (i : m) (j : m') : ((N * N : ℕ) : k) * (b * x * b') i j ∈ 𝒪[k] := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine sum_mem fun a _ => sum_mem fun c _ => ?_
  have : ((N * N : ℕ) : k) * (b i c * x c a * b' a j) = ((N : k) * b i c) * x c a * ((N : k) * b' a j) := by
    push_cast; ring
  rw [this]
  exact mul_mem (mul_mem (hb i c) (hx c a)) (hb' a j)

end GlobalTheory.FinPl.RdInt

theorem GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × n => β.b x.1 x.2) (fun x : n' × Fin S.rank => α.b' x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  refine ⟨K * (N₀ * N₀), Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀), fun t ht hrd => ?_⟩
  have hent := GlobalTheory.FinPl.RdInt.entry_mem β.b α.b' (fun i a => h₀ (Sum.inl (i, a))) (fun a j => h₀ (Sum.inr (a, j)))
    (rd α β t) hrd
  have htw := GlobalTheory.FinPl.HalfInd.wr_rd α β ht
  have hu : IsHalf p.e ((N₀ * N₀) • t) := (GlobalTheory.PlaceModel.isHalf_iff S T).2
    ((GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) _)
  have hui : ∀ i j, toEAf D (((N₀ * N₀) • t) i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have h1 : ((N₀ * N₀) • t) i j = p.sec (((N₀ * N₀ : ℕ) : k) * (β.b * rd α β t * α.b') i j) := by
      rw [← nsmul_eq_mul, map_nsmul, ← GlobalTheory.FinPl.HalfInd.wr_apply, htw]
      rfl
    rw [h1]
    exact GlobalTheory.PlaceCoord.toEAf_mem ((p.int_iff _).1 (hent i j))
  have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) hu) hui
  have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h1).1
  have hh : K • (N₀ * N₀) • t ∈ GlobalTheory.PlaceModel.half S T p.e :=
    (GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) _
  rw [(GlobalTheory.PlaceModel.mem_half S T).1 hh] at h2
  rwa [mul_nsmul']

end

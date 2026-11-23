import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
open NumberField

noncomputable section

open scoped Classical

namespace GlobalTheory.RatPointSum

variable {F : Type} [Field F] [NumberField F]

theorem norm_mixedEmbedding_le_sum (x : F) : ‖mixedEmbedding F x‖ ≤ ∑ w : InfinitePlace F, w x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => AbsoluteValue.nonneg _ _)
    (Finset.mem_univ w)

theorem norm_mixedEmbedding_nat_mul_le {κ : Type} [Fintype κ] (M : ℕ) (ξ : κ → F) :
    ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ (M : ℝ) * ∑ i, ∑ w : InfinitePlace F, w (ξ i) := by
  have h0 : ∀ i, 0 ≤ ∑ w : InfinitePlace F, w (ξ i) := fun i => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [map_mul, map_natCast, ← nsmul_eq_mul]
  refine norm_nsmul_le.trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_mixedEmbedding_le_sum (ξ i)).trans ?_) (Nat.cast_nonneg M)
  exact Finset.single_le_sum (f := fun i => ∑ w : InfinitePlace F, w (ξ i)) (fun i _ => h0 i) (Finset.mem_univ i)

end GlobalTheory.RatPointSum

open GlobalTheory.RatPointSum in

theorem GlobalTheory.RatPointSum.norm_thetaSum_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (M : ℕ) (B : ℝ) (Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ), 1 ≤ M →
      (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ≠ 0 → ∀ i, ∃ o : 𝓞 F, (M : F) * ξ i = o) →
      (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)) ^ N ≤ B) →
      ‖GlobalTheory.WeilM.thetaSum F Ψ‖ ≤ C * B * (M : ℝ) ^ N := by
  intro F _ _ κ _
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ one_pos
  set L := GlobalTheory.WeilM.denomLattice F κ 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  have hLn : ∀ z : L, 0 ≤ ((1 + ‖z‖) ^ r)⁻¹ := fun z => inv_nonneg.2 (by positivity)
  refine ⟨r, ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹, tsum_nonneg hLn, ?_⟩
  intro M B Ψ hM hsupp hdec
  have hB : 0 ≤ B := le_trans (by positivity) (hdec 0)
  let S : Set (κ → F) := {ξ | ∀ i, ∃ o : 𝓞 F, (M : F) * ξ i = o}
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F ((M : F) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding F ((M : F) * ξ i) ∈ mixedEmbedding.integerLattice F
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : F) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i)))
  let G : (κ → F) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact (hL.comp_injective hj).mul_left _
  have hbound : ∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0
    · rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace F, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  calc ‖GlobalTheory.WeilM.thetaSum F Ψ‖ ≤ ∑' ξ, G ξ := tsum_of_norm_bounded hGs.hasSum hbound
    _ = ∑' ξ : S, B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ := (tsum_subtype S _).symm
    _ = B * (M : ℝ) ^ r * ∑' ξ : S, (fun z : L => ((1 + ‖z‖) ^ r)⁻¹) (j ξ) := tsum_mul_left
    _ ≤ B * (M : ℝ) ^ r * ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hL hLn hj) (by positivity)
    _ = _ := by ring

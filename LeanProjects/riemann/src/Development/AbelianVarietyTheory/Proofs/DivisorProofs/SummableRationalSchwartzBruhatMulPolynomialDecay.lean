import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LatSumSB

open GlobalTheory.WeilM GlobalTheory.ThetaTrCont

theorem summable_sb_mul_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ *
        ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  intro F _ _ κ _ g hg a
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hK : IsCompact ((fun z => z - a) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hK
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, fun c => ?_⟩
  set M := Module.finrank ℤ (denomLattice F κ N) + 1
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine mul_eq_zero_of_left ?_ _
    rw [norm_eq_zero]
    by_contra h0
    apply hξ
    have hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ (fun z => z - a) '' tsupport g :=
      ⟨_, subset_tsupport _ h0, by funext i; simp⟩
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy'⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hKN _ hy i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy'
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_norm_bounded
      ((((summable_one_add_norm_inv (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj).mul_left
        ((1 + ‖c‖) ^ M)).mul_left B) fun ξ => ?_
    set z : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ.1 i)
    have hz : ‖(j ξ : denomLattice F κ N)‖ = ‖z‖ := rfl
    simp only [Function.comp_apply, hz]
    have hpos1 : 0 < (1 + ‖z + c‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hpos2 : 0 < (1 + ‖z‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hw : ((1 + ‖z + c‖) ^ M)⁻¹ ≤ (1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos2, ← div_eq_inv_mul, div_le_iff₀ hpos1, ← mul_pow, mul_comm (1 + ‖c‖)]
      exact pow_le_pow_left₀ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)).le (one_add_norm_le z c) M
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (inv_nonneg.2 hpos1.le)]
    calc ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i) + a i)‖ * ((1 + ‖z + c‖) ^ M)⁻¹
        ≤ B * ((1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹) :=
          mul_le_mul (hB _) hw (inv_nonneg.2 hpos1.le) ((norm_nonneg _).trans (hB 0))
      _ = _ := rfl

end GlobalTheory.LatSumSB

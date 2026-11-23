import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PurityDepth

theorem hasDepth_scaled : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  intro k _ _ _ _ A' C _ _ _ _ ϖ P Ψ hΨ hϖ
  have hΨ' : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix A' C k) := hΨ
  have hϖ' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := fun x => by rw [hϖ, le_uniformizer_iff]
  obtain ⟨Λ, hΛ, hinv⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k A' C Ψ hΨ'
  let f : (A' × C → k) → Matrix A' C k := fun z => Matrix.of fun i j => z (i, j)
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_apply (i, j)
  have hΛn : f ⁻¹' (Λ : Set (Matrix A' C k)) ∈ nhds (0 : A' × C → k) :=
    (hΛ.preimage hf).mem_nhds (by
      show f 0 ∈ Λ
      exact (show f 0 = 0 from rfl) ▸ Λ.zero_mem)
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ q : A' × C, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix A' C k => x q.1 q.2) '' tsupport Ψ ⊆ GlobalTheory.SplitWeil.cball (ϖ ^ e)⁻¹ := fun q =>
    GlobalTheory.AdaptedExp.eventually_subset_cball hϖ' (hc.image (by fun_prop))
  obtain ⟨M, hM1, hM2⟩ := ((Filter.eventually_all.2 h1).and (GlobalTheory.AdaptedExp.eventually_box_subset hϖ' hΛn)).exists
  refine ⟨M, fun n hn => ?_⟩

  set w := valuation k (ϖ : k) with hw
  have hw1 : w ≤ 1 := hϖ.mem
  set u := valuation k ((ϖ ^ M : kˣ) : k) with hu
  have hu0 : 0 < u := zero_lt_iff.2 (by simp [hu])
  have huw : u = w ^ M := by rw [hu, Units.val_pow_eq_pow_val, map_pow]
  have hinvu : valuation k (((ϖ ^ M)⁻¹ : kˣ) : k) = u⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hn' : valuation k ((ϖ ^ n : kˣ) : k) ≤ u * u := by
    rw [Units.val_pow_eq_pow_val, map_pow, huw, ← pow_add, ← two_mul]
    exact pow_le_pow_right_of_le_one' hw1 hn
  have hd : ∀ (X : Matrix A' C k) i j, (X * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) i j = X i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)) :=
    fun X i j => mul_diagonal _ _ _ _
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · by_contra hne
    apply hY
    have hs := subset_tsupport _ hne
    have he : ∀ i j, valuation k (Y i j * (if j ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k))) ≤ u⁻¹ :=
      fun i j => by
        have := hM1 (i, j) ⟨_, hs, rfl⟩
        simpa only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, hd, hinvu] using this
    refine GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
    · have h := he i j
      rw [if_pos hj, map_mul, ← hu] at h
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j) ≤ u * u * valuation k (Y i j) :=
            mul_le_mul_left hn' _
        _ = u * (valuation k (Y i j) * u) := by rw [mul_assoc, mul_comm u (valuation k (Y i j))]
        _ ≤ u * u⁻¹ := mul_le_mul_right h _
        _ = 1 := mul_inv_cancel₀ hu0.ne'
    · have h := he i j
      rw [if_neg hj, map_mul, hinvu] at h
      rw [Valuation.mem_integer_iff]
      have := mul_le_mul_left h u
      rwa [mul_assoc, inv_mul_cancel₀ hu0.ne', mul_one] at this
  · obtain ⟨h1, h2⟩ := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.1 hZ
    show Ψ ((Y + Z) * _) = Ψ (Y * _)
    rw [Matrix.add_mul]
    refine hinv _ _ ?_
    refine hM2 (fun q => (Z * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k)
      else (((ϖ ^ M)⁻¹ : kˣ) : k))) q.1 q.2) ?_
    unfold GlobalTheory.StepData.box
    intro q
    beta_reduce
    rw [hd, map_mul, ← hu]
    by_cases hj : q.2 ∈ P
    · rw [if_pos hj, ← hu]
      calc valuation k (Z q.1 q.2) * u ≤ 1 * u := mul_le_mul_left (h1 q.1 q.2 hj) _
        _ = u := one_mul u
    · rw [if_neg hj, hinvu]
      calc valuation k (Z q.1 q.2) * u⁻¹ ≤ u * u * u⁻¹ := mul_le_mul_left ((h2 q.1 q.2 hj).trans hn') _
        _ = u := by rw [mul_assoc, mul_inv_cancel₀ hu0.ne', mul_one]

end GlobalTheory.PurityDepth

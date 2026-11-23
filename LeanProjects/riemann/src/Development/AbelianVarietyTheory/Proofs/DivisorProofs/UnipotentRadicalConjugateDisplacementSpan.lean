import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix

namespace GlobalTheory.UnipCol

theorem sub_one_ne_zero_lt {K : Type} [Field K] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ} {e : (Σ a, m a) ≃ Fin N} {u : GL (Fin N) K}
    (hu : u ∈ GlobalTheory.SmGL.unipRad K e) {k j : Fin N} (h : (u.1 - 1) k j ≠ 0) :
    (e.symm k).1 < (e.symm j).1 := by
  obtain ⟨hp, hd⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective k
  obtain ⟨⟨b, l⟩, rfl⟩ := e.surjective j
  simp only [Equiv.symm_apply_apply]
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with hlt | heq
  · apply h
    have h0 := GlobalTheory.SmGL.mem_parab_iff.1 hp a b i l hlt
    have hne : e ⟨a, i⟩ ≠ e ⟨b, l⟩ := fun hh => by
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    rw [Matrix.sub_apply, h0, Matrix.one_apply_ne hne, sub_zero]
  · subst heq
    apply h
    rw [Matrix.sub_apply, hd b i l]
    by_cases hil : i = l
    · subst hil; simp
    · have hne : e ⟨b, i⟩ ≠ e ⟨b, l⟩ := fun hh => hil (by
        have := e.injective hh
        simpa using this)
      rw [Matrix.one_apply_ne hil, Matrix.one_apply_ne hne, sub_zero]

theorem conj_sub_one_mulVec_mem : ∀ {K : Type} [Field K] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ} (e : (Σ a, m a) ≃ Fin N) (u : GL (Fin N) K),
    u ∈ GlobalTheory.SmGL.unipRad K e → ∀ (B : GL (Fin N) K) (z : Fin N → K),
    ((B * u * B⁻¹).1 - 1) *ᵥ z ∈ Submodule.span K ((fun k a => B.1 a k) ''
      {k | ∃ j, (e.symm k).1 < (e.symm j).1 ∧ ((B⁻¹).1 *ᵥ z) j ≠ 0}) := by
  intro K _ α m _ _ _ _ N e u hu B z
  have hM : (B * u * B⁻¹).1 - 1 = B.1 * (u.1 - 1) * (B⁻¹).1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
  set w := (B⁻¹).1 *ᵥ z with hw
  rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_eq_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [op_smul_eq_smul]
  by_cases hk : ((u.1 - 1) *ᵥ w) k = 0
  · rw [hk, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_, rfl⟩)
    rw [Matrix.mulVec, dotProduct] at hk
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    exact ⟨j, sub_one_ne_zero_lt hu (left_ne_zero_of_mul hj), right_ne_zero_of_mul hj⟩

end GlobalTheory.UnipCol

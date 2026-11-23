import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Formalism.LatticeTheta.Statement

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

section
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem inner_remb_eq_trace (a b : F) :
    ⟪remb F a, remb F b⟫ = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by
  rw [GlobalTheory.trace_eq_sum_realEmbeddings, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [map_mul, mul_comm]

theorem remb_mem_dual_latOf_iff (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) (ν : F) :
    remb F ν ∈ Formalism.H.dual (latOf N) ↔ ν ∈ FractionalIdeal.dual ℤ ℚ N := by
  rw [Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule, FractionalIdeal.mem_dual hN]
  constructor
  · intro h a ha
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (h (remb F a) ((mem_latOf N _).mpr ⟨a, ha, rfl⟩))
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    have : ((z : ℚ) : ℝ) = ((Algebra.trace ℚ F (ν * a) : ℚ) : ℝ) := by
      have h2 : ((z : ℤ) : ℝ) = ⟪remb F ν, remb F a⟫ := by simpa using hz
      rw [inner_remb_eq_trace] at h2
      exact_mod_cast h2
    exact_mod_cast this
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := (mem_latOf N y).mp hy
    obtain ⟨z, hz⟩ := h a ha
    rw [Algebra.traceForm_apply] at hz
    refine Submodule.mem_one.mpr ⟨z, ?_⟩
    rw [show (innerₗ (RSp F)) (remb F ν) (remb F a) = ⟪remb F ν, remb F a⟫ from rfl,
      inner_remb_eq_trace, ← hz]
    simp

theorem exists_remb_eq_of_mem_dual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F)
    (N : FractionalIdeal (𝓞 F)⁰ F) (hbN : ∀ i, b i ∈ N) (μ : RSp F)
    (hμ : μ ∈ Formalism.H.dual (latOf N)) : ∃ ν : F, remb F ν = μ := by
  set B := Algebra.traceForm ℚ F
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ F
  set b' := B.dualBasis hB b
  have hdel : ∀ i j, Algebra.trace ℚ F (b' j * b i) = if i = j then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
    rwa [Algebra.traceForm_apply] at this
  have hc : ∀ i, ∃ z : ℤ, ⟪μ, remb F (b i)⟫ = z := fun i => by
    have := (LinearMap.BilinForm.mem_dualSubmodule _).mp hμ (remb F (b i))
      ((mem_latOf N _).mpr ⟨b i, hbN i, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp this
    exact ⟨z, by simpa using hz.symm⟩
  choose c hc using hc
  set ν : F := ∑ j, (c j : ℚ) • b' j
  have hνb : ∀ i, ⟪remb F ν, remb F (b i)⟫ = c i := fun i => by
    rw [inner_remb_eq_trace]
    have : Algebra.trace ℚ F (ν * b i) = c i := by
      simp only [ν, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hdel, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this]; simp
  have hind : LinearIndependent ℝ (fun i => remb F (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun w => ⟪w, remb F (b' j)⟫) hg
    simp only [sum_inner, real_inner_smul_left, inner_remb_eq_trace, inner_zero_left] at this
    simp only [mul_comm (b _) (b' j), hdel] at this
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi]; simp) (by simp)] at this
    simpa using this
  have hcard : Fintype.card ι = Module.finrank ℝ (RSp F) := by
    rw [finrank_euclideanSpace, GlobalTheory.card_realEmbeddings, Module.finrank_eq_card_basis b]
  haveI : Nonempty ι := b.index_nonempty
  let E := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hz : innerₛₗ ℝ (μ - remb F ν) = 0 := E.ext fun i => by
    simp [E, inner_sub_left, hνb, hc]
  have h0 := LinearMap.congr_fun hz (μ - remb F ν)
  have h1 : ⟪μ - remb F ν, μ - remb F ν⟫ = 0 := by
    rw [LinearMap.zero_apply] at h0; exact h0
  rw [inner_self_eq_zero, sub_eq_zero] at h1
  exact ⟨ν, h1.symm⟩

end

theorem dual_latOf_eq_latOf_traceDual (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  classical
  ext μ
  constructor
  · intro hμ
    rw [mem_latOf]
    let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hbN : ∀ i, basisOfFractionalIdeal F I i ∈ N := fun i => by
      have := (mem_span_basisOfFractionalIdeal F (I := I) (x := basisOfFractionalIdeal F I i)).mp
        (Submodule.subset_span ⟨i, rfl⟩)
      simpa [I] using this
    obtain ⟨ν, hν⟩ := exists_remb_eq_of_mem_dual (basisOfFractionalIdeal F I) N hbN μ hμ
    subst hν
    exact ⟨ν, (remb_mem_dual_latOf_iff N hN ν).mp hμ, rfl⟩
  · intro hμ
    obtain ⟨ν, hν, rfl⟩ := (mem_latOf _ μ).mp hμ
    exact (remb_mem_dual_latOf_iff N hN ν).mpr hν

end GlobalTheory.LipschitzTR

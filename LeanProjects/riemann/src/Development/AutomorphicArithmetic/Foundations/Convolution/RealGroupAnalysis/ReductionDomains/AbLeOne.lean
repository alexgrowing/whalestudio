import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BorHomeo

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem UpperTheory.ConvolutionTheory.R2.M.pow_form {F : Type} [Field F] [NumberField F] (b : A F) (a : (A F)ˣ) (n : ℕ) :
    ∃ c : A F, (nU b * mD a) ^ n = nU c * mD (a ^ n) := by
  induction n with
  | zero => exact ⟨0, by simp [M.nU_zero, M.mD_one]⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + ((a ^ n : (A F)ˣ) : A F) ^ 2 * b, ?_⟩
    rw [pow_succ (nU b * mD a), hc, pow_succ a, M.mD_mul, M.nU_add]
    simp only [mul_assoc]
    rw [← mul_assoc (mD (a ^ n)) (nU b), M.mD_mul_nU]
    simp only [mul_assoc]

private theorem UpperTheory.ConvolutionTheory.R2.M.inv_form {F : Type} [Field F] [NumberField F] (b : A F) (a : (A F)ˣ) :
    ∃ c : A F, (nU b * mD a)⁻¹ = nU c * mD a⁻¹ := by
  refine ⟨((a⁻¹ : (A F)ˣ) : A F) ^ 2 * (-b), ?_⟩
  rw [_root_.mul_inv_rev, ← M.mD_inv, ← M.nU_neg, M.mD_mul_nU]

private theorem UpperTheory.ConvolutionTheory.R2.M.ab_pow {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (n : ℕ) :
    ab (a ^ n) = ab a ^ n := by
  induction n with
  | zero => simp [M.ab_one]
  | succ n ih => rw [pow_succ, pow_succ, M.ab_mul, ih]

private theorem UpperTheory.ConvolutionTheory.R2.M.ab_le_one {F : Type} [Field F] [NumberField F] (U : Set (IdeleGroup F)) (hU : IsCompact U)
    (a : (A F)ˣ) (h : ∀ n : ℕ, a ^ n ∈ U) : ab a ≤ 1 := by
  obtain ⟨C, hC⟩ := (hU.image (M.continuous_ab (F := F))).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have := hC (Set.mem_image_of_mem _ (h n))
  rw [M.ab_pow] at this
  exact absurd hn (not_lt.mpr this)

theorem UpperTheory.ConvolutionTheory.R2.M.borK :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ U : Set (IdeleGroup F), IsCompact U ∧ ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hK' : IsCompact ((Subtype.val : M.Bor F → G1 F) ⁻¹' KK F) := hemb.isCompact_preimage hKc
  let U : Set (IdeleGroup F) := Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹' KK F))
  have hU : IsCompact U := (hK'.image e.symm.continuous).image continuous_fst
  have mem : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → a ∈ U := by
    intro b a h
    refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
    change ((e (a, b) : M.Bor F) : G1 F) ∈ KK F
    rw [he]; exact h
  have le : ∀ (b : A F) (a : (A F)ˣ), nU b * mD a ∈ KK F → ab a ≤ 1 := by
    intro b a h
    refine M.ab_le_one U hU a fun n => ?_
    obtain ⟨c, hc⟩ := M.pow_form b a n
    refine mem c _ ?_
    rw [← hc, hK]
    rw [hK] at h
    exact (M.Ks F).pow_mem h n
  refine ⟨U, hU, fun b a h => ⟨mem b a h, le_antisymm (le b a h) ?_⟩⟩
  obtain ⟨c, hc⟩ := M.inv_form b a
  have h2 : nU c * mD a⁻¹ ∈ KK F := by
    rw [← hc, hK]
    rw [hK] at h
    exact (M.Ks F).inv_mem h
  have h3 := le c _ h2
  rw [M.ab_inv] at h3
  exact (inv_le_one₀ (M.ab_pos a)).mp h3

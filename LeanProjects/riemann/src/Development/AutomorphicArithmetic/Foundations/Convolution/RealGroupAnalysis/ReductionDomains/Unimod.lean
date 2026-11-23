import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.unimod :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (μ : Measure (G1 F)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro F _ _ μ _
  have h0 : ∀ g : G1 F, (Measure.modularCharacter g : ℝ≥0) ≠ 0 := fun g h => by
    have e := map_mul (Measure.modularCharacter (G := G1 F)) g g⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at e
    exact one_ne_zero e
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h3F : (3 : F) ≠ 0 := by norm_num
  let two : (A F)ˣ := Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 2 h2F)
  have h2 : (two : A F) = 2 := map_ofNat (algebraMap F (A F)) 2
  have h4 : ∀ b : A F, (Measure.modularCharacter (nU (4 * b)) : ℝ≥0) = Measure.modularCharacter (nU b) := by
    intro b
    have e := congrArg (Measure.modularCharacter (G := G1 F)) (M.mD_mul_nU two b)
    rw [map_mul, map_mul, mul_comm] at e
    have c := mul_right_cancel₀ (h0 _) e
    rw [h2] at c
    norm_num at c
    exact c.symm
  have hn : ∀ c : A F, (Measure.modularCharacter (nU c) : ℝ≥0) = 1 := by
    intro c
    have h3 : (3 : A F) * (rt (3⁻¹ : F) * c) = c := by
      have : (3 : A F) * rt (3⁻¹ : F) = 1 := by
        rw [show (3 : A F) = rt (3 : F) from (map_ofNat (algebraMap F (A F)) 3).symm, ← map_mul, mul_inv_cancel₀ h3F, map_one]
      rw [← mul_assoc, this, one_mul]
    set b : A F := rt (3⁻¹ : F) * c with hb
    have e := h4 b
    rw [show (4 : A F) * b = 3 * b + b by ring, M.nU_add, map_mul, h3] at e
    exact mul_right_cancel₀ (h0 (nU b)) (e.trans (one_mul _).symm)
  have hw : (Measure.modularCharacter (wW F) : ℝ≥0) = 1 := by
    have e : wW F * wW F * (wW F * wW F) = 1 := by
      refine Subtype.ext ?_
      rw [M.val_mul, M.val_mul]
      ext i j; fin_cases i <;> fin_cases j <;> simp [wW, Matrix.mul_apply, Fin.sum_univ_two]
    have e' := congrArg (Measure.modularCharacter (G := G1 F)) e
    rw [map_mul, map_mul, map_one] at e'
    have e4 : (Measure.modularCharacter (wW F) : ℝ≥0) ^ 4 = 1 := by rw [← e']; ring
    exact (pow_eq_one_iff.1 e4).resolve_right (by norm_num)
  have hall : ∀ g : G1 F, (Measure.modularCharacter g : ℝ≥0) = 1 := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
      rw [(gen F).1]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | hx
      · exact hn c
      · rw [Set.mem_singleton_iff.1 hx]; exact hw
    | one => exact map_one _
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, one_mul]
    | inv x _ hx =>
      have e := map_mul (Measure.modularCharacter (G := G1 F)) x x⁻¹
      rw [mul_inv_cancel, map_one, hx, one_mul] at e
      exact e.symm
  haveI : μ.InnerRegular := inferInstance
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from hall g, one_smul]

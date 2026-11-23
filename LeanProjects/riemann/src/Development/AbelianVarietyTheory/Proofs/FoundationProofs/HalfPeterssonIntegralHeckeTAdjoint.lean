import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonDoubleCosetAdjointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightGamma0CosetDecompositionAdjugateHeckeTStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma adjT_adj_adj (M : M2) : M.adjugate.adjugate = M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]

lemma intMatrixTwo_adjugate_zero_zero (M : M2) : M.adjugate 0 0 = M 1 1 := by
  simp [Matrix.adjugate_fin_two]

lemma pet_const_mul_left (k : ℕ) (ρ : ℍ → ℝ) (c : ℂ) (F G : ℍ → ℂ) :
    pet k ρ (fun τ => c * F τ) G = conj c * pet k ρ F G := by
  unfold pet
  rw [← integral_const_mul]
  congr 1; funext τ
  simp only [map_mul]; ring

end GlobalTheory.EisM

theorem GlobalTheory.EisM.pet_To_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → q.Prime → ¬ q ∣ L → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (To k (ch ε q) q a)) = ch ε q * pet k ρ (qs (To k (ch ε q) q h)) (qs a) := by
  intro k L N q ε ρ h a hk hL hNL hq hqL hρ hh ha
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNL hL
  have hqN : ¬ q ∣ N := fun h' => hqL (h'.trans hNL)
  have hcop : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
  have hq0 : 0 < q := hq.pos
  have hε1 : ch ε 1 = 1 := by simp [ch]
  obtain ⟨-, hTaeq⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) a hk hq0 hε1 ha.1
  obtain ⟨-, hTheq⟩ := GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k q (ch ε) h hk hq0 hε1 hh.1.1
  have hcont_h := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have hcont_a := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha.1).2
  have hslz := GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk
  have hdetpos : ∀ i, 0 < (repT q i).det := by
    intro i; cases i <;> simp [repT, repU, Matrix.det_fin_two_of, hq0]
  have hlow : ∀ i, (repT q i) 1 0 = 0 := by
    intro i; cases i <;> simp [repT, repU]
  have hint : ∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * slz k (repT q i) (qs a) τ * (τ.im : ℂ) ^ k)) :=
    fun i => GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ (slz k (repT q i) (qs a)) hk hL hNL hρ hh
      ((hslz.2.2.2.1 _ (hdetpos i) hcont_a).aestronglyMeasurable)
      (GlobalTheory.T.hasModerateGrowth_algebra_slash_stable.2.2 _ k _ (hdetpos i) (hlow i) (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha.1))
  have hadj := GlobalTheory.T.petersson_doubleCoset_adjoint k L N q ε ρ (DT L q) (Option (Fin q)) (Option (Fin q)) (repT q)
    (fun i => (repT q i).adjugate) (qs h) (qs a) hk hN hNL hq0 hcop hρ
    (fun δ hδ => ⟨hδ.1, (Int.natCast_dvd_natCast.2 hNL).trans hδ.2⟩)
    (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL) (GlobalTheory.T.rightGamma0CosetDecomposition_adjugate_heckeT L q hq hqL) hh.1.2 ha.2 hcont_h hcont_a hint
  rw [← hTaeq] at hadj
  rw [hadj]

  have hu : ((q : ℤ) : ZMod N) = ((ZMod.unitOfCoprime q hcop : (ZMod N)ˣ) : ZMod N) := by
    simp [ZMod.coe_unitOfCoprime]
  have hnorm : ‖ch ε q‖ = 1 := by
    simp only [ch]; rw [hu]; exact DirichletCharacter.unit_norm_eq_one ε _
  have hne : ch ε q ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hinvq : ch ε⁻¹ q = (ch ε q)⁻¹ := by
    simp only [ch]; rw [MulChar.inv_apply_eq_inv']
  have hinv1 : ch ε⁻¹ 1 = 1 := by simp [ch]
  have hsumeq : (fun τ => ∑ j, ch ε⁻¹ ((repT q j).adjugate 0 0) * slz k (repT q j).adjugate.adjugate (qs h) τ)
      = fun τ => (ch ε q)⁻¹ * qs (To k (ch ε q) q h) τ := by
    funext τ
    rw [hTheq]
    simp only [hsum, Fintype.sum_option, adjT_adj_adj, intMatrixTwo_adjugate_zero_zero, Finset.mul_sum, mul_add]
    simp [repT, repU, hinvq, hinv1, hε1, hne]
  rw [hsumeq, pet_const_mul_left]
  have hc : conj ((ch ε q)⁻¹) = ch ε q := by
    rw [map_inv₀]
    have : conj (ch ε q) * ch ε q = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]; simp
    exact inv_eq_of_mul_eq_one_right this
  rw [hc]

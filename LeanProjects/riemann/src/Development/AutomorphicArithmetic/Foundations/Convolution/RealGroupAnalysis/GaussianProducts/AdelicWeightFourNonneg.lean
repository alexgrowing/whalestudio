import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoefBd
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatLin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_cD (s : (A F)ˣ) : Continuous (cD s : G1 F → G1 F) := by
  refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
  have he : ∀ i j, Continuous fun g : G1 F => g.1 i j := fun i j =>
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact he 0 0
  · exact (he 0 1).mul continuous_const
  · exact continuous_const.mul (he 1 0)
  · exact he 1 1

private theorem cD_cD_inv (s : (A F)ˣ) (k : G1 F) : cD s (cD s⁻¹ k) = k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD, mul_assoc]

private theorem infOrth_cD {s : (A F)ˣ} (h1 : (s : A F).1 = 1) (h2 : ((s⁻¹ : (A F)ˣ) : A F).1 = 1)
    {k : G1 F} (hk : InfOrth k) : InfOrth (cD s k) := by
  have hm : ∀ a b : A F, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have hent : ∀ i j, ((cD s k).1 i j).1 = (k.1 i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (k.1 0 1 * ((s⁻¹ : (A F)ˣ) : A F)).1 = _
      rw [hm, h2, mul_one]
      rfl
    · change ((s : A F) * k.1 1 0).1 = _
      rw [hm, h1, one_mul]
      rfl
    · rfl
  intro i j
  have e : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
  have h := hk i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, e, Matrix.transpose_apply, Matrix.transpose_apply] at h ⊢
  rw [hent, hent, hent, hent]
  exact h

private theorem adelicWeightFour_mono {L L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    (h : (L : FractionalIdeal (𝓞 F)⁰ F) ≤ L') (N : ℕ) (v : V4 F) : wt4 L N v ≤ wt4 L' N v :=
  Finset.prod_le_prod (fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _)
    fun i _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_mono h N (v i)

private theorem adelicWeightFour_nonneg (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (v : V4 F) : 0 ≤ wt4 L N v :=
  Finset.prod_nonneg fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _

private theorem common_majorant {n : ℕ} (Ψ : Fin n → V4 F → ℂ)
    (hΨ : ∀ i, Ψ i ∈ schwartzBruhatPi F (Fin 4)) (N : ℕ) :
    ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧ ∀ i v, ‖Ψ i v‖ ≤ B * wt4 L N v := by
  have one : ∀ i, ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧
      ∀ v, ‖Ψ i v‖ ≤ B * wt4 L N v := by
    intro i
    obtain ⟨M, L, hM, hb⟩ := GlobalTheory.CompanionTheory.EpConvB.exists_majorant (hΨ i)
      (isCompact_singleton (x := (1 : GL (Fin 4) (A F)))) N
    refine ⟨M, L, hM, fun v => ?_⟩
    have h := hb 1 rfl v
    simpa [wt4] using h
  choose B L hB hb using one
  have key : ∀ s : Finset (Fin n), ∃ (B' : ℝ) (L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B' ∧
      ∀ i ∈ s, ∀ v, ‖Ψ i v‖ ≤ B' * wt4 L' N v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, 1, le_rfl, by simp⟩
    | insert a s _ ih =>
      obtain ⟨B', L', h0, h⟩ := ih
      refine ⟨B a + B', fractionalIdealSupUnit (L a) L', add_nonneg (hB a) h0, fun i hi v => ?_⟩
      have hl : wt4 (L a) N v ≤ wt4 (fractionalIdealSupUnit (L a) L') N v :=
        adelicWeightFour_mono le_sup_left N v
      have hr : wt4 L' N v ≤ wt4 (fractionalIdealSupUnit (L a) L') N v :=
        adelicWeightFour_mono le_sup_right N v
      have hw := adelicWeightFour_nonneg (fractionalIdealSupUnit (L a) L') N v
      rcases Finset.mem_insert.1 hi with rfl | hi
      · calc ‖Ψ i v‖ ≤ B i * wt4 (L i) N v := hb i v
          _ ≤ B i * wt4 (fractionalIdealSupUnit (L i) L') N v :=
            mul_le_mul_of_nonneg_left hl (hB i)
          _ ≤ (B i + B') * wt4 (fractionalIdealSupUnit (L i) L') N v :=
            mul_le_mul_of_nonneg_right (by linarith) hw
      · calc ‖Ψ i v‖ ≤ B' * wt4 L' N v := h i hi v
          _ ≤ B' * wt4 (fractionalIdealSupUnit (L a) L') N v :=
            mul_le_mul_of_nonneg_left hr h0
          _ ≤ (B a + B') * wt4 (fractionalIdealSupUnit (L a) L') N v :=
            mul_le_mul_of_nonneg_right (by linarith [hB a]) hw
  obtain ⟨B', L', h0, h⟩ := key Finset.univ
  exact ⟨B', L', h0, fun i v => h i (Finset.mem_univ i) v⟩

end UpperTheory.ConvolutionTheory.R2.G

theorem UpperTheory.ConvolutionTheory.R2.G.majL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ((nu F h : (A F)ˣ) : A F).1 = 1 → ∀ N : ℕ,
    ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧ ∀ k ∈ KK F, ∀ v, ‖hat (W.Om k (W.L h φ)).1 v‖ ≤ B * wt4 L N v := by
  intro F E _ _ _ _ _ _ _ D W φ hφ h ht N
  have hinv : (((nu F h)⁻¹ : (A F)ˣ) : A F).1 = 1 := by
    have h1 : (((nu F h : (A F)ˣ) : A F) * (((nu F h)⁻¹ : (A F)ˣ) : A F)).1 = (1 : A F).1 := by
      rw [Units.mul_inv]
    have h2 : (((nu F h : (A F)ˣ) : A F) * (((nu F h)⁻¹ : (A F)ˣ) : A F)).1 =
        ((nu F h : (A F)ˣ) : A F).1 * (((nu F h)⁻¹ : (A F)ˣ) : A F).1 := rfl
    rw [h2, ht, one_mul] at h1
    exact h1
  have hC : IsCompact (cD (nu F h)⁻¹ '' KK F) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2.image (continuous_cD _)
  have hO : ∀ k ∈ cD (nu F h)⁻¹ '' KK F, InfOrth k := by
    rintro _ ⟨k, hk, rfl⟩
    exact infOrth_cD hinv (by rw [inv_inv]; exact ht) hk.1
  obtain ⟨U, -, hU, hm⟩ := (fockSt F E D W).om φ hφ _ hC hO
  obtain ⟨n, b, c, B, -, -, hb⟩ := coefBd F E D W φ _ U hC hU hm
  obtain ⟨H, hH⟩ := hatLin F
  obtain ⟨B', L, hB', hmaj⟩ := common_majorant (fun i => (H (W.L h (b i))).1)
    (fun i => (H (W.L h (b i))).2) N
  refine ⟨n * (|B| * B'), L, by positivity, fun k hk v => ?_⟩
  obtain ⟨hc, he⟩ := hb _ ⟨k, hk, rfl⟩
  have hcomm : W.Om k (W.L h φ) = W.L h (W.Om (cD (nu F h)⁻¹ k) φ) := by
    have h1 := LinearMap.congr_fun (W.comm h (cD (nu F h)⁻¹ k)) φ
    rw [cD_cD_inv] at h1
    exact h1.symm
  have hexp : hat (W.Om k (W.L h φ)).1 v =
      ∑ i, c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v := by
    rw [hcomm, he, ← hH, map_sum, map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hexp]
  have hw := adelicWeightFour_nonneg L N v
  calc ‖∑ i, c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v‖
      ≤ ∑ i, ‖c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, |B| * (B' * wt4 L N v) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul ((hc i).trans (le_abs_self B)) (hmaj i v) (norm_nonneg _) (abs_nonneg B)
    _ = n * (|B| * B') * wt4 L N v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

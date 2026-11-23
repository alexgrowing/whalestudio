import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitPairNondegF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

variable (σ JS JT) in

def pairMat (y : WOF F E nS nT) : Matrix (Fin nS) (Fin nT) (AEF F E) :=
  (JS⁻¹).map (incAF F E) * (y.map (cAF σ))ᵀ * JT.map (incAF F E)

theorem pairMat_apply (y : WOF F E nS nT) (a : Fin nS) (d : Fin nT) :
    pairMat σ JS JT y a d = ∑ b, ∑ c, incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) := by
  simp only [pairMat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hOF_single (y : WOF F E nS nT) (d₀ : Fin nT) (a₀ : Fin nS) (t : AEF F E) :
    hOF σ JS JT (Matrix.single d₀ a₀ t) y = pairMat σ JS JT y a₀ d₀ * t := by
  rw [pairMat_apply, Finset.sum_mul, hOF, Finset.sum_eq_single a₀]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single d₀]
    · rw [Matrix.single_apply_same]
    · intro d _ hd
      rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hd h.1.symm), mul_zero]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.single_apply_of_ne _ _ _ _ _ (fun h => ha h.2.symm), mul_zero]
  · simp

theorem pairMat_ne_zero (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) {y : WOF F E nS nT}
    (hy : y ≠ 0) : pairMat σ JS JT y ≠ 0 := by
  intro h0
  apply hy
  have huS : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have huT : IsUnit JT.det := isUnit_iff_ne_zero.mpr hT.2
  have hL : JS.map (incAF F E) * (JS⁻¹).map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ huS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hR : JT.map (incAF F E) * (JT⁻¹).map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ huT, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (y.map (cAF σ))ᵀ = 0 := by
    calc (y.map (cAF σ))ᵀ = JS.map (incAF F E) * pairMat σ JS JT y * (JT⁻¹).map (incAF F E) := by
          rw [pairMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_assoc, hR,
            Matrix.mul_one]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  have := congrFun (congrFun hY j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at this
  rw [Matrix.zero_apply, ← GlobalTheory.HeisLineF.cAF_cAF σ hσ (y i j), this, map_zero]

theorem exists_detect (hσ : ∀ x, σ (σ x) = x) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hS : IsHermND σ JS)
    (hT : IsHermND σ JT) {ξ₀ : E} (hξ0 : ξ₀ ≠ 0) (hξ : σ ξ₀ = -ξ₀) {e : AEF F E} (he : IsSplitIdemF σ e)
    {y : WOF F E nS nT} (hyY : ∀ i j, cAF σ e * y i j = y i j) (hy : y ≠ 0) :
    ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧
      ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) ≠ 1 := by
  have hM := pairMat_ne_zero hσ hS hT hy
  obtain ⟨a₀, d₀, had⟩ : ∃ a d, pairMat σ JS JT y a d ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext hc)
  have hcc : cAF σ (cAF σ e) = e := GlobalTheory.HeisLineF.cAF_cAF σ hσ e
  have hMe : pairMat σ JS JT y a₀ d₀ * e = pairMat σ JS JT y a₀ d₀ := by
    rw [pairMat_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
      conv_lhs => rw [← hyY c b]
      rw [map_mul, hcc]
    linear_combination (-(incAF F E (JS⁻¹ a₀ b) * incAF F E (JT c d₀))) * e1
  have hunit : incAF F E ξ₀⁻¹ * incAF F E ξ₀ = 1 := by rw [← map_mul, inv_mul_cancel₀ hξ0, map_one]
  have hm0 : incAF F E ξ₀ * pairMat σ JS JT y a₀ d₀ ≠ 0 := by
    intro h0
    apply had
    calc pairMat σ JS JT y a₀ d₀ = incAF F E ξ₀⁻¹ * (incAF F E ξ₀ * pairMat σ JS JT y a₀ d₀) := by
          rw [← mul_assoc, hunit, one_mul]
      _ = 0 := by rw [h0, mul_zero]
  obtain ⟨z, hz⟩ := GlobalTheory.AdelicTraceNondeg.trace_pairing_nondeg F E ψ hψ _ hm0
  refine ⟨Matrix.single d₀ a₀ (e * z), fun i j => ?_, ?_⟩
  · by_cases hij : d₀ = i ∧ a₀ = j
    · obtain ⟨rfl, rfl⟩ := hij
      rw [Matrix.single_apply_same, ← mul_assoc, he.1]
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij, mul_zero]
  · rw [GlobalTheory.FinLatF.symplOHF_skew σ JS JT hσ hS hT ξ₀ hξ y, sub_neg_eq_add, GlobalTheory.FinLatF.symplOHF_add_self, symplOF,
      hOF_single, ← mul_assoc (pairMat σ JS JT y a₀ d₀) e z, hMe, ← mul_assoc]
    exact hz

theorem detect_conj_half : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ e, IsSplitIdemF σ e →
      ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) → y ≠ 0 →
        ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧
          ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) ≠ 1 := by
  intro F E _ _ _ _ _ σ hσ ψ hψ nS nT JS JT hS hT ξ₀ hξ0 hξ e he y hyY hy
  exact exists_detect hσ hψ hS hT hξ0 hξ he hyY hy

theorem sigma_sigma_of_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

end GlobalTheory.SplitPairNondegF

end

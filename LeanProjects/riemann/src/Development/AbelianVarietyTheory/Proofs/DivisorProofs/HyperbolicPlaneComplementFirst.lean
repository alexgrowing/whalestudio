import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicative
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviPlaneHom

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviHom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_flip_skew (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (skew : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) : form σ J v w = -σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [skew]
  ring

def skew2 : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0]

theorem gram_block_skew (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {b : ℕ} (W : Spc F E (b + 2)) (W₁ : Spc F E b)
    (H : Plane E (b + 2) b) (skew : ∀ i j, σ (W.J j i) = -W.J i j)
    (hxx : form σ W.J H.x H.x = 0) (hyy : form σ W.J H.y H.y = 0) (hxy : form σ W.J H.x H.y = 1)
    (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J) :
    (fromCols H.ι (cols2 H.x H.y))ᵀ * W.J * (fromCols H.ι (cols2 H.x H.y)).map σ = fromBlocks W₁.J 0 0 skew2 := by
  have hmap : (fromCols H.ι (cols2 H.x H.y)).map σ = fromCols (H.ι.map σ) ((cols2 H.x H.y).map σ) := by
    ext i (j | j) <;> rfl
  have ho : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by rw [mulVec_single_one]; rfl
  have orth' : ∀ j, form σ W.J (fun i => H.ι i j) H.x = 0 ∧ form σ W.J (fun i => H.ι i j) H.y = 0 := fun j => by
    rw [ho]; exact horth _
  rw [hmap, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hgram]
  congr 1
  · ext j k
    rw [form_gram, ho]
    fin_cases k
    · simpa [cols2] using (horth (Pi.single j 1)).1
    · simpa [cols2] using (horth (Pi.single j 1)).2
  · ext k j
    rw [form_gram, form_flip_skew σ hσ skew]
    fin_cases k
    · simp [cols2, (orth' j).1]
    · simp [cols2, (orth' j).2]
  · ext k k'
    rw [form_gram]
    fin_cases k <;> fin_cases k' <;>
      simp [cols2, skew2, hxx, hyy, hxy, form_flip_skew σ hσ skew H.y H.x]

theorem levi_section_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ a b, M (a * b) = M a * M b) ∧ ∀ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H t 1 m → ∀ y, m * M y = M y * m := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ _ M hM
  subst hn
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero, mul_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * W.J * P.map σ = fromBlocks W₁.J 0 0 skew2 :=
    gram_block_skew σ hσ W W₁ H hskew hxx hyy hxy horth hgram
  set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks W₁.J 0 0 skew2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [skew2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * W.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * W.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h h' : UA σ W.J), IsLevi (W₁ := W₁) H l g₀ h →
      IsLevi (W₁ := W₁) H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by
      rw [← Matrix.mul_one (mat h), ← Matrix.mul_one (mat h'), ← hPQ', ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        levi_mul_cols H l g₀ h hL, levi_mul_cols H l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  refine ⟨fun a b => ?_, fun t m hm y => ?_⟩
  · have h2 := isLevi_mul H (hM a) (hM b)
    rw [mul_one] at h2
    exact huniq _ _ _ _ (hM (a * b)) h2
  · have h1 := isLevi_mul H hm (hM y)
    have h2 := isLevi_mul H (hM y) hm
    rw [mul_one, one_mul] at h1
    rw [mul_one, one_mul] at h2
    exact huniq _ _ _ _ h1 h2

end GlobalTheory.LeviPlaneHom

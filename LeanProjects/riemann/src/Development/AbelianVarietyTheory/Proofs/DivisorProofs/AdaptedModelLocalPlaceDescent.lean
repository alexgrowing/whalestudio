import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.IsoOrthLocA

open GlobalTheory.IsoOrthLoc GlobalTheory.MixedLagr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem wfac_zero (σ : E →ₐ[F] E) {d d₁ : ℕ} (JW : Matrix (Fin d) (Fin d) E) (w : Fin d → E)
    (ι : Matrix (Fin d) (Fin d₁) E) (h : ∀ q, form σ JW w (fun l => ι l q) = 0) (z : Fin d₁ → AE F E) :
    ∑ j, ∑ l, incV F w j * incM F JW j l * cA σ ((incM F ι *ᵥ z) l) = 0 := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have e1 : ∑ j, ∑ l, incV F w j * incM F JW j l * cA σ ((incM F ι *ᵥ z) l) =
      ∑ q, inclR (F := F) (AF F) (form σ JW w (fun l => ι l q)) * cA σ (z q) := by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, incV, incM, Matrix.map_apply,
      Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e1]
  simp [h]

theorem isoA_iso_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ u ∈ isoA (F := F) H H', At (evFin F v) u → ∀ u' ∈ isoA (F := F) H H', At (evFin F v) u' →
      (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u').2 -
        (GlobalTheory.LatVac.locCo M.co v u').1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M hB hX hW hH hH' v
  have hσ := sigma_sigma hB.cm
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl

  have key2 : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
      ∀ u' ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)},
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 := by
    rintro u ⟨y, rfl⟩ u' ⟨z, rfl⟩
    have hq : ∀ q, form σ W.J H'.x (fun l => H'.ι l q) = 0 := by
      intro q
      have e : (fun l => H'.ι l q) = H'.ι *ᵥ Pi.single q 1 := by
        funext l; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [e, form_skew hσ hW.skew, (hH'.orth _).1, map_zero, neg_zero]
    rw [symp, hTens_vecMulVec, wfac_zero σ W.J H'.x H'.ι hq z, mul_zero, mul_zero, map_zero]

  have key4 : ∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)},
      ∀ u' ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)},
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 := by
    rintro u ⟨z, rfl⟩ u' ⟨z', rfl⟩
    have h : ∑ i, ∑ k, incV F H.x i * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      have h1 := congrArg (inclR (F := F) (AF F)) hH.xx
      rw [map_zero] at h1
      rw [← h1]
      simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
        mul_assoc]
    rw [symp, hTens_vecMulVec, h, zero_mul, mul_zero, map_zero]
  intro u hu _ u' hu' _
  rcases hu with hu | hu <;> rcases hu' with hu' | hu'
  · rw [locCo_form M.co v u u', symplectic_isotropic_plane_vanishes F E σ n d d₁ X.J W.J H' hH'.xx u hu u' hu', map_zero]
  · rw [locCo_form M.co v u u', key2 u hu u' hu', map_zero]
  · have h := locCo_form M.co v u' u
    rw [key2 u' hu' u hu, map_zero] at h
    linear_combination -h
  · rw [locCo_form M.co v u u', key4 u hu u' hu', map_zero]

end GlobalTheory.IsoOrthLocA

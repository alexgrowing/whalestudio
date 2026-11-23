import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.IsoBLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem pair_zero_of_form (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x x' : Fin n → E)
    (h0 : form σ J x x' = 0) :
    ∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x' k) = 0 := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have h1 := congrArg (inclR (F := F) (AF F)) h0
  rw [map_zero] at h1
  rw [← h1]
  simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]

theorem pair_iota_left (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (x : Fin n → E) (h0 : ∀ u, form σ J (ι *ᵥ u) x = 0) (y : Fin n₁ → AE F E) :
    ∑ i, ∑ k, (incM F ι *ᵥ y) i * incM F J i k * cA σ (incV F x k) = 0 := by
  classical
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have hq : ∀ q, ∑ i, ∑ k, inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k) = 0 := by
    intro q
    have h1 := congrArg (inclR (F := F) (AF F)) (h0 (Pi.single q 1))
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, map_sum, map_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e : ∀ i k, (incM F ι *ᵥ y) i * incM F J i k * cA σ (incV F x k) =
      ∑ q, y q * (inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k)) := by
    intro i k
    simp only [Matrix.mulVec, dotProduct, incM, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have sw : ∀ i, ∑ k, ∑ q, y q * (inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k)) =
      ∑ q, ∑ k, y q * (inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k)) := fun i => Finset.sum_comm
  simp only [e, sw]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [← Finset.mul_sum]
  rw [hq q, mul_zero]

theorem pair_conj (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → AE F E) :
    ∑ i, ∑ k, a i * incM F J i k * cA σ (b k) = cA σ (∑ i, ∑ k, b i * incM F J i k * cA σ (a k)) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [map_sum, map_mul, GlobalTheory.IsoOrthLoc.cA_cA hσ, incM, Matrix.map_apply, hc, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.IsoBLoc

namespace GlobalTheory.IsoBLoc

theorem isoB_locCo_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M : Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ v : Pl F, ∀ u ∈ isoB (F := F) H H', At (evFin F v) u → ∀ u' ∈ isoB (F := F) H H', At (evFin F v) u' →
      (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u').2 -
        (GlobalTheory.LatVac.locCo M.co v u').1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ X X₁ W W₁ H H' M hB hX hW hH hH' v u hu _ u' hu' _
  have hσ := GlobalTheory.IsoOrthLoc.sigma_sigma hB.cm
  rw [GlobalTheory.IsoOrthLoc.locCo_form M.co v u u']
  suffices hs : symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 by rw [hs, map_zero]
  have hxx := pair_zero_of_form (F := F) σ X.J H.x H.x hH.xx
  have hww := pair_zero_of_form (F := F) σ W.J H'.x H'.x hH'.xx
  have hl : ∀ y, ∑ i, ∑ k, (incM F H.ι *ᵥ y) i * incM F X.J i k * cA σ (incV F H.x k) = 0 :=
    pair_iota_left σ X.J H.ι H.x (fun u => (hH.orth u).1)
  have hr : ∀ y, ∑ i, ∑ k, incV F H.x i * incM F X.J i k * cA σ ((incM F H.ι *ᵥ y) k) = 0 := by
    intro y
    rw [pair_conj σ hσ X.J hX.herm, hl y, map_zero]
  rcases hu with ⟨z, rfl⟩ | ⟨y, rfl⟩ <;> rcases hu' with ⟨z', rfl⟩ | ⟨y', rfl⟩
  · rw [symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hxx, zero_mul, mul_zero, map_zero]
  · rw [symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hr, zero_mul, mul_zero, map_zero]
  · rw [symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hl, zero_mul, mul_zero, map_zero]
  · rw [symp, GlobalTheory.MixedLagr.hTens_vecMulVec, hww, mul_zero, mul_zero, map_zero]

end GlobalTheory.IsoBLoc

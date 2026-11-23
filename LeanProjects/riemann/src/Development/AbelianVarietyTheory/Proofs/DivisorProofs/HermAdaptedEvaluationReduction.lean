import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.IsoPhaseComm

theorem rho_swap {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (s u : V) (φ : (κ → R) → ℂ) :
    d.rho ψ s (d.rho ψ u φ) = ψ (Bf s u) • d.rho ψ u (d.rho ψ s φ) := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, d.form, ← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [add_right_comm x (d.e s).1]
  congr 2
  simp only [add_dotProduct]
  ring

theorem hTens_pure {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (JA : Matrix α α E) (JB : Matrix β β E) (a b : α → E) (p q : β → E) :
    hTens c JA JB (Matrix.vecMulVec a p) (Matrix.vecMulVec b q) =
      (∑ i, ∑ k, a i * JA i k * c (b k)) * ∑ j, ∑ l, p j * JB j l * c (q l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem thetaSum_smul {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem symp_pair {σ : E →ₐ[F] E} {n n₁ d₁ : ℕ} (hσ : ∀ e, σ (σ e) = e) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (JW : Matrix (Fin d₁) (Fin d₁) E) (H : Plane E n n₁)
    (hxy : form σ J H.x H.y = 1) (w : Fin d₁ → E) (z : Fin d₁ → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW) (Matrix.vecMulVec (incV F H.y) (incV F w))
      (Matrix.vecMulVec (incV F H.x) z) = -Algebra.trace (AF F) (AE F E) (GlobalTheory.UnipMass.hA σ JW (incV F w) z) := by
  have hyx : form σ J H.y H.x = 1 := by
    have h1 : σ (form σ J H.x H.y) = form σ J H.y H.x := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [← h1, hxy, map_one]
  have h0 : (∑ i, ∑ k, incV F H.y i * incM F J i k * cA σ (incV F H.x k)) = 1 := by
    have : (∑ i, ∑ k, incV F H.y i * incM F J i k * cA σ (incV F H.x k)) =
        inclR (F := F) (AF F) (form σ J H.y H.x) := by
      simp only [incV, incM, Matrix.map_apply, GlobalTheory.ThK.UnipDom.Inverse.cA_inclR, form, dotProduct, Matrix.mulVec,
        map_sum, map_mul, Finset.mul_sum, mul_assoc]
    rw [this, hyx, map_one]
  have h2 : (∑ j, ∑ l, incV F w j * incM F JW j l * cA σ (z l)) = GlobalTheory.UnipMass.hA σ JW (incV F w) z := by
    simp only [GlobalTheory.UnipMass.hA, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [symp, hTens_pure, h0, h2, one_mul, neg_one_mul, map_neg]

end GlobalTheory.ThK.IsoPhaseComm

namespace GlobalTheory.ThK.IsoPhaseComm

theorem thetaSum_ev_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁) (r s n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ)
    (M₂ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁,
    IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → ∀ φ ∈ schA F (Fin n × Fin d₁),
    ∀ (w : Fin d₁ → E) (z : Fin d₁ → AE F E),
      thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) φ))) =
        B.ψ (-Algebra.trace (AF F) (AE F E) (GlobalTheory.UnipMass.hA σ W₁.J (incV F w) z)) *
          thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) := by
  intro F E _ _ _ _ _ σ B n d₁ X W₁ M₁ r s n₁ X₁ H j₀ j₁ M₂ hB hX hH e' he' φ hφ w z
  have hσ : ∀ e, σ (σ e) = e := GlobalTheory.ThK.UnipDom.Inverse.sigma_sigma hB.cm
  have hsch := GlobalTheory.HeisSchA.rho_mem_schA M₁ B.ψ hB.std (Matrix.vecMulVec (incV F H.y) (incV F w)) φ hφ
  rw [rho_swap M₁.co B.ψ, map_smul, he'.inv _ ⟨z, rfl⟩ _ hsch, thetaSum_smul,
    symp_pair hσ X.J hX.herm W₁.J H hH.xy w z]

end GlobalTheory.ThK.IsoPhaseComm

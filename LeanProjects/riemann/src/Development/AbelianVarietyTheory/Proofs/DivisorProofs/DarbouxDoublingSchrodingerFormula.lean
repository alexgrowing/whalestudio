import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLaw

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.OrthHeisPhase

theorem transpose_mulVec_eq_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d d₁ : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E) (x : Fin d → E)
    (h : ∀ u, form σ J (ι *ᵥ u) x = 0) : ιᵀ *ᵥ (J *ᵥ fun k => σ (x k)) = 0 := by
  funext m
  have := h (Pi.single m 1)
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem hTens_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (y : Fin n ⊕ Fin n → AE F E) (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)),
      hTens (cA σ) (incM F W.J) (dbl (incM F X.J)) (incM F H'.ι * z) (Matrix.vecMulVec (incV F H'.x) y) = 0 := by
  intro F E _ _ _ _ _ σ B n d X W d₁ W₁ H' i₀ i₁ hA y z
  set v : Fin d → AE F E := incM F W.J *ᵥ fun k => cA σ (incV F H'.x k) with hv
  have h0 : (incM F H'.ι)ᵀ *ᵥ v = 0 := by
    have e := transpose_mulVec_eq_zero σ W.J H'.ι H'.x (fun u => (hA.orth u).1)
    funext m
    have := congrArg (inclR (F := F) (AF F)) (congrFun e m)
    have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
    simpa [hv, incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul, hc] using this
  have h1 : (incM F H'.ι * z)ᵀ *ᵥ v = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  set b := incM F H'.ι * z with hb
  have step : ∀ i j, (∑ k, ∑ l, b i j * incM F W.J i k * dbl (incM F X.J) j l *
      cA σ (Matrix.vecMulVec (incV F H'.x) y k l)) = b i j * v i * ∑ l, dbl (incM F X.J) j l * cA σ (y l) := by
    intro i j
    simp only [hv, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.vecMulVec_apply, map_mul]
    ring
  simp only [hTens]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => step i j, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun h1 j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
  rw [← Finset.sum_mul, this, zero_mul]

theorem rho_vecMulVec_add_orth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
      (ψ : AddChar (AF F) ℂ) (y : Fin n ⊕ Fin n → AE F E) (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E))
      (φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
      dd.rho ψ (Matrix.vecMulVec (incV F H'.x) y) (dd.rho ψ (incM F H'.ι * z) φ) =
        dd.rho ψ (Matrix.vecMulVec (incV F H'.x) y + incM F H'.ι * z) φ := by
  intro F E _ _ _ _ _ σ B n d X W d₁ W₁ H' i₀ i₁ hA dd ψ y z φ
  have hz := hTens_eq_zero F E σ B n d X W d₁ W₁ H' i₀ i₁ hA y z
  have hba : symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J)) (incM F H'.ι * z) (Matrix.vecMulVec (incV F H'.x) y) = 0 := by
    simp [symp, hz]
  have hab : symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J)) (Matrix.vecMulVec (incV F H'.x) y) (incM F H'.ι * z) = 0 := by
    have e1 := dd.form (Matrix.vecMulVec (incV F H'.x) y) (incM F H'.ι * z)
    have e2 := dd.form (incM F H'.ι * z) (Matrix.vecMulVec (incV F H'.x) y)
    rw [hba] at e2
    linear_combination e1 + e2
  rw [GlobalTheory.InertRhoLaw.darboux_rho_rho, hab, mul_zero, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.OrthHeisPhase

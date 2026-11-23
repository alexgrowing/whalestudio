import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneFactor

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.LeviEvLaw

theorem sum_reorder {R : Type} [AddCommMonoid R] {α β μ : Type} [Fintype α] [Fintype β] [Fintype μ]
    (G : α → β → α → β → μ → R) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, G i j k l m) = ∑ m, ∑ j, ∑ l, ∑ i, ∑ k, G i j k l m := by
  calc _ = ∑ i, ∑ j, ∑ k, ∑ m, ∑ l, G i j k l m :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ m, ∑ k, ∑ l, G i j k l m :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ m, ∑ j, ∑ k, ∑ l, G i j k l m := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, G i j k l m := Finset.sum_comm
    _ = ∑ m, ∑ j, ∑ i, ∑ k, ∑ l, G i j k l m := Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ j, ∑ i, ∑ l, ∑ k, G i j k l m :=
          Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

theorem sum_tensor_eq_zero {R : Type} [CommRing R] {α β μ : Type} [Fintype α] [Fintype β] [Fintype μ]
    (a : α → μ → R) (u : β → μ → R) (A : α → α → R) (B : β → β → R) (xv : α → R) (yv : β → R)
    (h : ∀ m, ∑ i, ∑ k, a i m * A i k * xv k = 0) :
    ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, a i m * u j m) * A i k * B j l * (xv k * yv l) = 0 := by
  have e : ∀ i j k l, (∑ m, a i m * u j m) * A i k * B j l * (xv k * yv l) =
      ∑ m, (a i m * A i k * xv k) * (u j m * B j l * yv l) := fun i j k l => by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp_rw [e]
  rw [sum_reorder (fun i j k l m => (a i m * A i k * xv k) * (u j m * B j l * yv l))]
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  have : ∑ i, ∑ k, (a i m * A i k * xv k) * (u j m * B j l * yv l) =
      (∑ i, ∑ k, a i m * A i k * xv k) * (u j m * B j l * yv l) := by
    simp only [Finset.sum_mul]
  rw [this, h m, zero_mul]

end GlobalTheory.LeviEvLaw

namespace GlobalTheory.LeviEvLaw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inner_eq_zero {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    {j₀ j₁ : ℕ} (hH : H.IsAdapted σ B X X₁ j₀ j₁) (m : Fin n₁) :
    ∑ i, ∑ k, incM F H.ι i m * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
  have h0 := (hH.orth (Pi.single m 1)).1
  have e : ∑ i, ∑ k, incM F H.ι i m * incM F X.J i k * cA σ (incV F H.x k) =
      inclR (F := F) (AF F) (form σ X.J (H.ι *ᵥ Pi.single m 1) H.x) := by
    rw [Matrix.mulVec_single_one]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [incM, incV, Matrix.map_apply]
    rw [mul_assoc]
    rfl
  rw [e, h0, map_zero]

end GlobalTheory.LeviEvLaw

namespace GlobalTheory.LeviEvLaw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symp_eq_zero {σ : E →ₐ[F] E} {B : Base F E} {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d}
    {H : Plane E n n₁} {j₀ j₁ : ℕ} (hH : H.IsAdapted σ B X X₁ j₀ j₁) (y : Fin d → AE F E)
    (u : Matrix (Fin d) (Fin n₁) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * uᵀ) (Matrix.vecMulVec (incV F H.x) y) = 0 := by
  have h : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * uᵀ) (Matrix.vecMulVec (incV F H.x) y) = 0 := by
    have := sum_tensor_eq_zero (fun i m => incM F H.ι i m) (fun j m => u j m) (fun i k => incM F X.J i k)
      (fun j l => incM F W.J j l) (fun k => cA σ (incV F H.x k)) (fun l => cA σ (y l)) (inner_eq_zero hH)
    rw [← this]
    simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, map_mul]
  simp only [symp, h, mul_zero, map_zero]

theorem ev_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), IsStd B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (y : Fin d → AE F E) (u : Matrix (Fin d) (Fin n₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * uᵀ) Φ) = M₁.co.rho B.ψ uᵀ (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M hψ n₁ X₁ H j₀ j₁ M₁ hH e he y u Φ hΦ
  have hs := symp_eq_zero (W := W) hH y u
  rw [M.co.form] at hs
  have hsplit : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * uᵀ) Φ =
      M.co.rho B.ψ (incM F H.ι * uᵀ) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y) Φ) := by
    rw [add_comm]
    simp only [Darboux.rho, map_add]
    exact GlobalTheory.LagrUniq.schr_add_of_orth B.ψ _ _ hs Φ
  have hq : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y) Φ ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ
  have hheis := he.Heisenberg₂ uᵀ _ hq
  rw [GlobalTheory.LagrUniq.incM_one, Matrix.transpose_one, Matrix.mul_one] at hheis
  rw [hsplit, hheis, he.inv _ ⟨y, rfl⟩ Φ hΦ]

end GlobalTheory.LeviEvLaw

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), IsStd B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ (y : Fin d → AE F E) (u : Matrix (Fin d) (Fin n₁) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d),
      e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * uᵀ) Φ) = M₁.co.rho B.ψ uᵀ (e Φ) :=
  GlobalTheory.LeviEvLaw.ev_law

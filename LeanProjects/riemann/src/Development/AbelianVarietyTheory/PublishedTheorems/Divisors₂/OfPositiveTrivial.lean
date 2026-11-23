import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup

noncomputable section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions
open scoped Matrix ENNReal

namespace GlobalTheory.Published

namespace GaussBonnet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mat_mul {P Q : ℕ} (g g' : UpqT P Q) : UpqT.mat (g * g') = UpqT.mat g * UpqT.mat g' := rfl

theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

def IsOrthFrame (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {P Q : ℕ}
    (B : Matrix (Fin r) (Fin P ⊕ Fin Q) ℂ) : Prop :=
  ∀ a b, hermC τ G (fun k => B k a) (fun k => B k b) = Formalism.UG.Jpq P Q a b

def realImage (Ψ : Finset (E →+* ℂ)) {P Q : Ψ → ℕ}
    (B : ∀ τ : Ψ, Matrix (Fin r) (Fin (P τ) ⊕ Fin (Q τ)) ℂ) (Γ : Subgroup (GL (Fin r) E)) :
    Subgroup (∀ τ : Ψ, UpqT (P τ) (Q τ)) where
  carrier := {g | ∃ γ ∈ Γ, ∀ τ : Ψ,
    B τ * UpqT.mat (g τ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * B τ}
  one_mem' := ⟨1, Γ.one_mem, fun τ => by simp [mat_one]⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨δ, hδ, hb⟩
    refine ⟨γ * δ, Γ.mul_mem hγ hδ, fun τ => ?_⟩
    rw [Pi.mul_apply, mat_mul, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Units.val_mul,
      Matrix.map_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨γ, hγ, ha⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, fun τ => ?_⟩
    have h1 : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul]; simp
    have h2 : UpqT.mat (a τ) * UpqT.mat (a⁻¹ τ) = 1 := by
      rw [← mat_mul, Pi.inv_apply, mul_inv_cancel, mat_one]
    calc B τ * UpqT.mat (a⁻¹ τ)
        = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * B τ) * UpqT.mat (a⁻¹ τ) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = _ := by rw [← ha, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem IsOrthFrame.exists_inv {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {P Q : ℕ}
    {B : Matrix (Fin r) (Fin P ⊕ Fin Q) ℂ} (hB : IsOrthFrame τ G B) (hr : P + Q = r) :
    Bᴴ * ((G.map τ).map (starRingEnd ℂ) * B) = Formalism.UG.Jpq P Q ∧
      ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin r) ℂ, C * B = 1 ∧ B * C = 1 := by
  have hJ : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have h1 : Bᴴ * ((G.map τ).map (starRingEnd ℂ) * B) = Formalism.UG.Jpq P Q := by
    ext a b
    have h := congrArg (starRingEnd ℂ) (hB a b)
    have h' : starRingEnd ℂ (Formalism.UG.Jpq P Q a b) = Formalism.UG.Jpq P Q a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
    rw [h'] at h
    rw [← h]
    simp [hermC, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  have h2 : (Formalism.UG.Jpq P Q * (Bᴴ * (G.map τ).map (starRingEnd ℂ))) * B = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, hJ]
  refine ⟨h1, _, h2, ?_⟩
  exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hr])).1 h2

end GaussBonnet

open GaussBonnet

def GaussBonnetUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (Γ : Subgroup (GL (Fin r) E)) (P Q : Ψ → ℕ)
    (B : ∀ τ : Ψ, Matrix (Fin r) (Fin (P τ) ⊕ Fin (Q τ)) ℂ) (c : CDHaar)
    (D : Set (∀ τ : Ψ, UpqT (P τ) (Q τ))),
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    (∀ τ, P τ + Q τ = r) → (∀ τ : Ψ, IsOrthFrame τ.1 G (B τ)) →
    (∀ γ ∈ Γ, ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) →
    Subgroup.Commensurable Γ (GlobalTheory.FiniteCovolume.uStabSubgroup G Λ) →
    (∀ γ ∈ Γ, ∀ (n : ℕ) (z : E), 0 < n →
      ((γ ^ n : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = z • (1 : Matrix (Fin r) (Fin r) E) → γ = 1) →
    IsFundamentalDomain (realImage Ψ B Γ) D (Measure.pi fun τ : Ψ => c.cd (P τ) (Q τ)) →
    ∃ n : ℕ, (Measure.pi fun τ : Ψ => c.cd (P τ) (Q τ)) D * ∏ τ : Ψ, (r.choose (P τ) : ℝ≥0∞) = n

namespace GaussBonnet

end GaussBonnet

end GlobalTheory.Published

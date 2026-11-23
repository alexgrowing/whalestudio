import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.CuspConjRad

open Formalism.UG (cT)

theorem conj_mem_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (C₀ C : Matrix (Fin n) (Fin r) E)
    (D D' : Matrix (Fin r) (Fin r) E), D * D' = 1 → D' * D = 1 → (γ.1 : Matrix (Fin n) (Fin n) E) * C₀ = C * D →
      ∀ g ∈ unipRad σ J C₀, ratEmb σ J γ * g * (ratEmb σ J γ)⁻¹ ∈ unipRad σ J C := by
  intro F E _ _ _ _ _ σ n r J γ C₀ C D D' hDD' hD'D hΓ g hg
  set Γ : Matrix (Fin n) (Fin n) E := (γ.1 : Matrix (Fin n) (Fin n) E) with hΓdef
  set Γi : Matrix (Fin n) (Fin n) E := ((γ.1⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hΓidef
  have h1 : Γ * Γi = 1 := by simp [Γ, Γi]
  have h2 : Γi * Γ = 1 := by simp [Γ, Γi]
  have hU : cT (σ : E →+* E) Γ * J * Γ = J := γ.2
  have hmul : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => Matrix.map_mul
  have hone : adMat F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hA1 : adMat F Γ * adMat F Γi = 1 := by rw [← hmul, h1, hone]
  have hA2 : adMat F Γi * adMat F Γ = 1 := by rw [← hmul, h2, hone]

  have hC : C = Γ * C₀ * D' := by rw [hΓ, Matrix.mul_assoc, hDD', Matrix.mul_one]
  have hΓiC : Γi * C = C₀ * D' := by rw [hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hTJ : cT (σ : E →+* E) Γ * J = J * Γi := by
    calc cT (σ : E →+* E) Γ * J = cT (σ : E →+* E) Γ * J * (Γ * Γi) := by rw [h1, Matrix.mul_one]
      _ = J * Γi := by rw [← Matrix.mul_assoc, hU]
  have hCJ : cT (σ : E →+* E) C * J = cT (σ : E →+* E) D' * (cT (σ : E →+* E) C₀ * J * Γi) := by
    rw [hC, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc, hTJ]
  have hDD : cT (σ : E →+* E) D * cT (σ : E →+* E) D' = 1 := by
    rw [← Formalism.UG.cT_mul, hD'D, Formalism.UG.cT_one]
  have hC₀J : cT (σ : E →+* E) C₀ * J * Γi = cT (σ : E →+* E) D * (cT (σ : E →+* E) C * J) := by
    rw [hCJ, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  let c := MulAut.conj (ratEmb σ J γ)
  have key : ∀ g : GAd σ J, (let m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 - 1
      m * adMat F C₀ = 0 ∧ adMat F (cT (σ : E →+* E) C₀ * J) * m = 0 ∧
      ∀ x : Fin n → E, (cT (σ : E →+* E) C₀ * J) *ᵥ x = 0 →
        ∃ a : Fin r → AF F ⊗[F] E, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F C₀ *ᵥ a) →
      (let m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J (c g)).1 - 1
      m * adMat F C = 0 ∧ adMat F (cT (σ : E →+* E) C * J) * m = 0 ∧
      ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 →
        ∃ a : Fin r → AF F ⊗[F] E, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F C *ᵥ a) := by
    intro g ⟨k1, k2, k3⟩
    set m := (matHom _ σ J g).1 - 1 with hm
    have hc : (matHom _ σ J (c g)).1 - 1 = adMat F Γ * m * adMat F Γi := by
      have e : (matHom _ σ J (c g)).1 = adMat F Γ * (matHom _ σ J g).1 * adMat F Γi := by
        rw [MulAut.conj_apply, ← map_inv, map_mul, map_mul]; rfl
      rw [e, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hA1]
    simp only [hc]
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · simp only [Matrix.mul_assoc]
      rw [← hmul Γi C, hΓiC, hmul C₀ D', ← Matrix.mul_assoc m, k1, Matrix.zero_mul, Matrix.mul_zero]
    · rw [hCJ, hmul (cT (σ : E →+* E) D') (cT (σ : E →+* E) C₀ * J * Γi), hmul (cT (σ : E →+* E) C₀ * J) Γi]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (adMat F Γi) (adMat F Γ), hA2, Matrix.one_mul,
        ← Matrix.mul_assoc (adMat F (cT (σ : E →+* E) C₀ * J)) m, k2, Matrix.zero_mul, Matrix.mul_zero]
    · have hy : (cT (σ : E →+* E) C₀ * J) *ᵥ (Γi *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hC₀J, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := k3 _ hy
      refine ⟨adMat F D *ᵥ a, ?_⟩
      have hv : (fun i => inclR (F := F) (AF F) ((Γi *ᵥ x) i)) = adMat F Γi *ᵥ (fun i => inclR (F := F) (AF F) (x i)) :=
        funext fun i => RingHom.map_mulVec _ _ _ i
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hv, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← hmul Γ C₀, ← hmul C D, hΓ]
  have hle : unipRad σ J C₀ ≤ (unipRad σ J C).comap c.toMonoidHom := by
    unfold unipRad
    rw [Subgroup.closure_le]
    intro g hg
    exact Subgroup.subset_closure (key g hg)
  exact hle hg

end GlobalTheory.CuspConjRad

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WittFrameSig

open Matrix

theorem Jpq_mul_self (r s : ℕ) : Formalism.UG.Jpq r s * Formalism.UG.Jpq r s = 1 := by
  simp [Formalism.UG.Jpq, fromBlocks_multiply]

theorem le_of_isotropic_diag {n r s k : ℕ} (hn : r + s = n) (J₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hA : Aᴴ * J₀ * A = Formalism.UG.Jpq r s)
    (X Y : Matrix (Fin n) (Fin k) ℂ) (hxx : Xᴴ * J₀ * X = 0) (hxy : Xᴴ * J₀ * Y = 1) : k ≤ r ∧ k ≤ s := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  set B : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ := Formalism.UG.Jpq r s * Aᴴ * J₀ with hB
  have hBA : B * A = 1 := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Jpq_mul_self]
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e).2 hBA
  have hJ : Bᴴ * Formalism.UG.Jpq r s * B = J₀ := by
    calc Bᴴ * Formalism.UG.Jpq r s * B = Bᴴ * (Aᴴ * J₀ * A) * B := by rw [hA]
      _ = (A * B)ᴴ * J₀ * (A * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by rw [hAB]; simp
  refine GlobalTheory.WittSignature.le_of_isotropic_standard (B * X) (Yᴴ * J₀ᴴ * A) ?_ ?_
  · calc Yᴴ * J₀ᴴ * A * (B * X) = Yᴴ * J₀ᴴ * (A * B) * X := by simp only [Matrix.mul_assoc]
      _ = (Xᴴ * J₀ * Y)ᴴ := by rw [hAB]; simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hxy, conjTranspose_one]
  · calc (B * X)ᴴ * Formalism.UG.Jpq r s * (B * X) = Xᴴ * (Bᴴ * Formalism.UG.Jpq r s * B) * X := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hJ, hxx]

end GlobalTheory.WittFrameSig

namespace GlobalTheory.WittFrameSig

open Matrix

theorem wittFrame_le_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  intro F E _ _ _ _ _ σ B n X r s hB hX r₀ Xf Yf hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hc : ∀ x, τ (σ x) = star (τ x) := hB.cm.2.2.2 τ
  obtain ⟨hrs, A, hA⟩ := hX.sig w
  have hmap : ∀ {a b : ℕ} (P : Matrix (Fin n) (Fin a) E) (Q : Matrix (Fin n) (Fin b) E),
      (Formalism.UG.cT (σ : E →+* E) P * ((1 : E) • X.J.map σ) * Q).map τ =
        (P.map τ)ᴴ * (X.J.map τ).map (starRingEnd ℂ) * Q.map τ := by
    intro a b P Q
    rw [one_smul, Matrix.map_mul, Matrix.map_mul]
    congr 2
    · ext i j
      simp [Formalism.UG.cT, conjTranspose_apply, hc]
    · ext i j
      simp [hc]
  have hA' : Aᴴ * (X.J.map τ).map (starRingEnd ℂ) * A = Formalism.UG.Jpq r s := by
    have h := congrArg (fun M => M.map (starRingEnd ℂ)) hA
    simp only [Matrix.map_mul] at h
    have hD : (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) = fromBlocks 1 0 0 (-1) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
    rw [hD] at h
    rw [Formalism.UG.Jpq, ← h]
    congr 2 <;> ext i j <;> simp [conjTranspose_apply]
  refine le_of_isotropic_diag hrs _ A hA' (Xf.map τ) (Yf.map τ) ?_ ?_
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittFrameSig

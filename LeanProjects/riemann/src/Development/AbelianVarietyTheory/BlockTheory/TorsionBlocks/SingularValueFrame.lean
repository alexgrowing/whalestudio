import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

section Matrices

variable {n : ℕ} (ε : Fin n → Bool)

def signMat : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if ε i then 1 else -1

def IsInU (g : Matrix (Fin n) (Fin n) ℂ) : Prop := gᴴ * signMat ε * g = signMat ε

def IsInK (k : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ ∀ i j, ε i ≠ ε j → k i j = 0

def IsInP (X : Matrix (Fin n) (Fin n) ℂ) : Prop := X.IsHermitian ∧ ∀ i j, ε i = ε j → X i j = 0

def realRank : ℕ := min (Fintype.card {i // ε i = true}) (Fintype.card {i // ε i = false})

def offBlock (X : Matrix (Fin n) (Fin n) ℂ) : Matrix {i // ε i = true} {i // ε i = false} ℂ :=
  Matrix.of fun i j => X i.1 j.1

def singVal (X : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin (offBlock ε X) :
    EuclideanSpace ℂ {i // ε i = false} →ₗ[ℂ] EuclideanSpace ℂ {i // ε i = true}).singularValues i

def coshProd (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∏ i ∈ Finset.range (realRank ε), Real.cosh (singVal ε X i)

def IsCartan (g X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsInP ε X ∧ ∃ k₁ k₂, IsInK ε k₁ ∧ IsInK ε k₂ ∧ g = k₁ * NormedSpace.exp X * k₂

theorem one_le_coshProd (X : Matrix (Fin n) (Fin n) ℂ) : 1 ≤ coshProd ε X :=
  Finset.prod_induction _ (fun r => 1 ≤ r) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl
    fun _ _ => Real.one_le_cosh _

example : IsInP ![true, false] !![0, 1; 1, 0] ∧ realRank ![true, false] = 1 := by
  refine ⟨⟨?_, fun i j h => ?_⟩, by decide⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · fin_cases i <;> fin_cases j <;> simp_all

end Matrices

def GramDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), IsInU ε g →
    (∃ X, IsCartan ε g X) ∧
    ∀ X, IsCartan ε g X → ((2 : ℂ)⁻¹ • (1 + g * gᴴ)).det = ((coshProd ε X ^ 2 : ℝ) : ℂ)

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}

def IsSignFrame (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def inFrame (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) : Matrix (Fin n) (Fin n) ℂ :=
  (b⁻¹ * AdelicU.matHom w.Completion σ J g * b).1.map (infEmb τ)

example : IsSignFrame σ (1 : Matrix (Fin n) (Fin n) E) (w := w) (fun _ => true) 1 := by
  simp [IsSignFrame, JR, cT_one]

end Place

def DoubledAbs : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (h : Q = dblGram finSumFinEquiv J)
      (w : InfinitePlace F) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)),
      IsSignFrame σ J ε b → ∀ g : GArch σ J w,
      (∃ p : siegelH w.Completion σ Q, ∃ k ∈ KArch σ Q w b, ioH w.Completion σ h (g, 1) = p * k) ∧
      hgtArch σ Q w b (ioH w.Completion σ h (g, 1)) ≤ 1 ∧
      (∃ X, IsCartan ε (inFrame σ J τ b g) X) ∧
      ∀ X, IsCartan ε (inFrame σ J τ b g) X →
        (hgtArch σ Q w b (ioH w.Completion σ h (g, 1)) : ℝ) = (coshProd ε X ^ 2)⁻¹ ∧
        (∀ (p : siegelH w.Completion σ Q), ∀ k ∈ KArch σ Q w b, ioH w.Completion σ h (g, 1) = p * k →
          ‖infEmb τ (aH w.Completion σ Q p).1‖ = (coshProd ε X)⁻¹) ∧
        ∀ (μ : (w.Completion ⊗[F] E)ˣ →* Circle) (s₀ s : ℂ) (Φ : GArch σ Q w → ℂ), Φ ∈ degPSArch σ Q w b μ s₀ →
          ∀ C : ℝ, (∀ k ∈ KArch σ Q w b, ‖Φ k‖ ≤ C) →
            ‖flatArch σ Q w b Φ s₀ s (ioH w.Completion σ h (g, 1))‖ ≤ C * coshProd ε X ^ (-(2 * s.re + (n : ℝ)))

def RealDoublingNorm : Prop := GramDet ∧ DoubledAbs

end GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

end

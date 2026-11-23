import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine

noncomputable section

open NumberField Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantHeightFlags

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j : ℕ}

def IsDetHeight (C : Matrix (Fin n) (Fin j) E) (K : Subgroup (GAd σ J)) (h : GAd σ J → ℝ) : Prop :=
  ∀ (p : GAd σ J) (B : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * B.1 →
    ∀ k ∈ K, h (p * k) = absE F E (GeneralLinearGroup.det B)

def IsRepSet (C : Matrix (Fin n) (Fin j) E) (T : Set (ratPts σ J)) : Prop :=
  Subgroup.IsComplement (((parFlag σ J C fun _ => 0).subgroupOf (ratPts σ J) : Subgroup (ratPts σ J)) : Set (ratPts σ J)) T

omit [NumberField E] in

theorem mem_parFlag_iff {C : Matrix (Fin n) (Fin j) E} {D : Matrix (Fin j) (Fin n) E} (hD : D * C = 1) (p : GAd σ J) :
    p ∈ parFlag σ J C (fun _ => 0) ↔
      ∃ B : GL (Fin j) (AF F ⊗[F] E), (matHom _ σ J p).1 * adMat F C = adMat F C * B.1 := by
  have hD' : adMat F D * adMat F C = 1 := by
    rw [← Matrix.map_mul, hD, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · rintro ⟨⟨A, -, eA⟩, A', -, eA'⟩
    have e : A * A' = 1 := by
      have : adMat F C * (A * A') = adMat F C := by
        rw [← Matrix.mul_assoc, ← eA, Matrix.mul_assoc, ← eA', ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
          mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]
      have h2 := congrArg (adMat F D * ·) this
      simpa only [← Matrix.mul_assoc, hD', Matrix.one_mul] using h2
    exact ⟨⟨A, A', e, mul_eq_one_comm.1 e⟩, eA⟩
  · rintro ⟨B, e⟩
    refine ⟨⟨B.1, fun _ _ h => absurd h (lt_irrefl _), e⟩, (B⁻¹).1, fun _ _ h => absurd h (lt_irrefl _), ?_⟩
    have : (matHom _ σ J p⁻¹).1 * ((matHom _ σ J p).1 * adMat F C) * (B⁻¹).1 = adMat F C * (B⁻¹).1 := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
    rw [← this, e, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

example (C : Matrix (Fin n) (Fin 0) E) (K : Subgroup (GAd σ J)) : IsDetHeight σ J C K fun _ => 1 := fun _ B _ _ _ => by
  rw [Subsingleton.elim B 1, map_one, map_one, NNReal.coe_one]

end

def EisensteinMaximalParabolic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ (j : ℕ) (hj : j ≤ r) (C : Matrix (Fin n) (Fin j) E), C = X.submatrix id (Fin.castLE hj) →
      (∀ g, ∃ p ∈ parFlag σ J C (fun _ => 0), ∃ k ∈ levelAll σ J L a, g = p * k) →
      ∀ h : GAd σ J → ℝ, IsDetHeight σ J C (levelAll σ J L a) h →
      ∀ φ : GAd σ J → ℂ, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) φ →
      ∃ Eis : ℂ → GAd σ J → ℂ,
        (∃ c : ℝ, ∀ T : Set (ratPts σ J), IsRepSet σ J C T → ∀ s : ℂ, c < s.re → ∀ g,
          Summable (fun t : T => ‖φ (t.1.1 * g) * (h (t.1.1 * g) : ℂ) ^ s‖) ∧
          Eis s g = ∑' t : T, φ (t.1.1 * g) * (h (t.1.1 * g) : ℂ) ^ s) ∧
        ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantHeightFlags

end

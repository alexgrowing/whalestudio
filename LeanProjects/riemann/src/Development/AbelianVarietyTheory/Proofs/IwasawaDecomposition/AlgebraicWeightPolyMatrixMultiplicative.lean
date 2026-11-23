import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPointsStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtMul

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def substL (A : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.C (A v.1 v.2.1 m) * MvPolynomial.X (v.1, m, v.2.2)

def substR (B : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.X (v.1, v.2.1, m) * MvPolynomial.C (B v.1 m v.2.2)

theorem eval_bind_substL (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q) =
      MvPolynomial.eval (upt (fun σ => A σ * Y σ)) Q := by
  calc MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt Y) (substL A v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt Y) (substL A v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt Y) (substL A v)) = upt (fun σ => A σ * Y σ) := by
        funext v
        simp [substL, upt, Matrix.mul_apply]
      rw [hf]

theorem eval_bind_substR (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q) =
      MvPolynomial.eval (upt (fun σ => X σ * B σ)) Q := by
  calc MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt X) (substR B v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt X) (substR B v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt X) (substR B v)) = upt (fun σ => X σ * B σ) := by
        funext v
        simp [substR, upt, Matrix.mul_apply]
      rw [hf]

theorem defectL_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt A) i m) * P m j) =
      evM P (upt (fun σ => A σ * Y σ)) i j - (evM P (upt A) * evM P (upt Y)) i j := by
  rw [map_sub, eval_bind_substL]
  simp [evM, Matrix.mul_apply]

theorem defectR_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) (P i j) -
        ∑ m, P i m * MvPolynomial.C (evM P (upt B) m j)) =
      evM P (upt (fun σ => X σ * B σ)) i j - (evM P (upt X) * evM P (upt B)) i j := by
  rw [map_sub, eval_bind_substR]
  simp [evM, Matrix.mul_apply]

theorem evM_ratPt (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hA : Agrees a b P)
    (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
  rw [hA γ γ₀ h]
  ext i j
  rfl

theorem ratPt_one :
    ratPt ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
  funext σ
  simp [ratPt]

theorem ratPt_mul (γ₀ γ₁ : GL (Fin n) L) :
    ratPt ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ := by
  funext σ
  simp [ratPt, Matrix.map_mul]

theorem evM_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧
      ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y →
        evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  intro L _ _ _ n a ι _ _ b P hA
  have h1 : evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 := by
    have hm : ((((1 : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [OneMemClass.coe_one, Units.val_one]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    rw [← ratPt_one, evM_ratPt a b P hA 1 1 hm, map_one, LinearMap.toMatrix_one]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ γ₁ : GL (Fin n) L, γ₁ ∈ GQ0 L n →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt (ratPt (γ₁ : Matrix (Fin n) (Fin n) L))) := by
    intro γ₀ h₀ γ₁ h₁
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h₀
    obtain ⟨γ', hγ'⟩ := exists_gq γ₁ h₁
    have hm : ((((γ * γ' : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [Subgroup.coe_mul, Units.val_mul, hγ, hγ', Matrix.map_mul]
    rw [← ratPt_mul, evM_ratPt a b P hA _ _ hm, evM_ratPt a b P hA _ _ hγ, evM_ratPt a b P hA _ _ hγ', map_mul,
      LinearMap.toMatrix_mul]
  have hL : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt Y →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * Y σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt Y) := by
    intro γ₀ h₀ Y hY
    ext i j
    have e := GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n (MvPolynomial.bind₁ (substL (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) i m) * P m j)
      (fun γ₁ h₁ => by rw [defectL_eval, hrat γ₀ h₀ γ₁ h₁, sub_self]) Y hY
    rw [defectL_eval, sub_eq_zero] at e
    exact e
  refine ⟨h1, fun X Y hX hY => ?_⟩
  ext i j
  have e := GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n (MvPolynomial.bind₁ (substR Y) (P i j) -
      ∑ m, P i m * MvPolynomial.C (evM P (upt Y) m j))
    (fun γ₀ h₀ => by rw [defectR_eval, hL γ₀ h₀ Y hY, sub_self]) X hX
  rw [defectR_eval, sub_eq_zero] at e
  exact e

end GlobalTheory.AlgWtMul

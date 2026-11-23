import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeightStatement

noncomputable section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem tauPt_one (τ : L →+* ℂ) : tauPt τ (1 : GL (Fin n) ℂ) = fun _ => 1 := by
  funext σ
  simp only [tauPt, inv_one, Units.val_one, Matrix.transpose_one]
  split_ifs <;> rfl

theorem tauPt_mul (τ : L →+* ℂ) (A B : GL (Fin n) ℂ) :
    tauPt τ (A * B) = fun σ => tauPt τ A σ * tauPt τ B σ := by
  funext σ
  simp only [tauPt]
  split_ifs
  · simp
  · simp [_root_.mul_inv_rev, Matrix.transpose_mul]
  · simp

open Classical in

def tauSubst (τ : L →+* ℂ) : (L →+* ℂ) × Fin n × Fin n →
    MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ := fun p =>
  if p.1 = τ then MvPolynomial.X (Sum.inl (p.2.1, p.2.2))
  else if p.1 = ComplexEmbedding.conjugate τ then MvPolynomial.X (Sum.inr (p.2.2, p.2.1))
  else MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)

theorem eval_evPt (τ : L →+* ℂ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (B : GL (Fin n) ℂ) :
    MvPolynomial.eval (evPt τ B) Q =
      MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2))
        (MvPolynomial.bind₁ (tauSubst τ) Q) := by
  have e := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ)
    (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) (tauSubst τ) Q
  erw [e]
  show MvPolynomial.eval _ Q = MvPolynomial.eval _ Q
  congr 2
  funext p
  simp only [evPt, tauSubst]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isPolyRep_evPt (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (h : Agrees a b P) (τ : L →+* ℂ) :
    IsPolyRep (fun B => evM P (evPt τ B)) := by
  obtain ⟨h1, hm⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n a ι b P h
  refine ⟨?_, ?_, ?_⟩
  · show evM P (evPt τ 1) = 1
    rw [evPt_eq_upt, tauPt_one]
    exact h1
  · intro A B
    show evM P (evPt τ (A * B)) = evM P (evPt τ A) * evM P (evPt τ B)
    rw [evPt_eq_upt, evPt_eq_upt, evPt_eq_upt, tauPt_mul]
    exact hm _ _ (isUPt_tauPt τ A) (isUPt_tauPt τ B)
  · intro i j
    refine ⟨MvPolynomial.bind₁ (tauSubst τ) (P i j), fun B => ?_⟩
    show MvPolynomial.eval (evPt τ B) (P i j) = _
    exact eval_evPt τ (P i j) B

end GlobalTheory.AlgWtHW

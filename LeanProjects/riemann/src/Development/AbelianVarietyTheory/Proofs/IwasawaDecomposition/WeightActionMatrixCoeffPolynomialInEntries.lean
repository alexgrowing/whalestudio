import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ActPolyCoeff

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def evPt (g : ι → GL (Fin n) K) : (ι ⊕ ι) × Fin n × Fin n → K := fun v =>
  Sum.elim (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)
    (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.2 v.2.1) v.1

def genSub (F : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial (ι × Fin n × Fin n) (MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K) :=
  MvPolynomial.eval₂ ((MvPolynomial.C).comp MvPolynomial.C)
    (fun v => ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (Sum.inl v.1, b, v.2.1)) * MvPolynomial.X (v.1, b, v.2.2)) F

theorem map_genSub (g : ι → GL (Fin n) K) (F : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.map (MvPolynomial.eval (evPt g)) (genSub F) = Formalism.L2.DIV.trAct g F := by
  unfold genSub
  rw [MvPolynomial.eval₂_comp_left]
  simp only [Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  congr 1
  · ext k; simp
  · funext v; simp [evPt, Matrix.transpose_apply]

end GlobalTheory.ActPolyCoeff

noncomputable section
namespace GlobalTheory.ActPolyCoeff

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem lin_map_eval {σ V : Type} (x : V → K) (ψ : MvPolynomial σ K →ₗ[K] K) (p : MvPolynomial σ (MvPolynomial V K)) :
    ψ (MvPolynomial.map (MvPolynomial.eval x) p) =
      MvPolynomial.eval x (∑ m ∈ p.support, p.coeff m * MvPolynomial.C (ψ (MvPolynomial.monomial m 1))) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, MvPolynomial.map_monomial, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_one (MvPolynomial.eval x (p.coeff m)), ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul, smul_eq_mul]
  simp

def detL (τ : ι) : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K :=
  (Matrix.of fun a b : Fin n => MvPolynomial.X (Sum.inl τ, a, b)).det

def detR (τ : ι) : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K :=
  (Matrix.of fun a b : Fin n => MvPolynomial.X (Sum.inr τ, b, a)).det

theorem eval_detL (g : ι → GL (Fin n) K) (τ : ι) :
    MvPolynomial.eval (evPt g) (detL τ) = ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
  unfold detL
  rw [RingHom.map_det]
  congr 1
  ext a b; simp [evPt]

theorem eval_detR (g : ι → GL (Fin n) K) (τ : ι) :
    MvPolynomial.eval (evPt g) (detR τ) = (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
  unfold detR
  rw [RingHom.map_det]
  congr 1
  ext a b; simp [evPt]

theorem detPow_eq (g : GL (Fin n) K) (e : ℤ) :
    Formalism.BasicNotions.detPow K n g e = if 0 ≤ e then ((g : Matrix (Fin n) (Fin n) K).det) ^ e.toNat
      else ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ (-e).toNat := by
  unfold Formalism.BasicNotions.detPow
  split_ifs with h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [zpow_natCast, Matrix.GeneralLinearGroup.val_det_apply]
  · have : e = -(((-e).toNat : ℕ) : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, ← inv_pow, ← map_inv]
    simp only [Int.toNat_natCast, neg_neg, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]

end GlobalTheory.ActPolyCoeff

noncomputable section
namespace GlobalTheory.ActPolyCoeff

def detTwPoly {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then detL τ ^ (lam τ).detShift.toNat else detR τ ^ (-(lam τ).detShift).toNat

theorem eval_detTwPoly {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : ι → GL (Fin n) K) : MvPolynomial.eval (evPt g) (detTwPoly lam) = Formalism.L2.DIV.detTwK lam g := by
  unfold detTwPoly Formalism.L2.DIV.detTwK
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [detPow_eq]
  split_ifs <;> simp [eval_detL, eval_detR]

theorem polyAction_coeff_poly : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (F : Formalism.L2.DIV.Pol K ι n)
    (ψ : Formalism.L2.DIV.Pol K ι n →ₗ[K] K), ∃ P : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K, ∀ g : ι → GL (Fin n) K,
    ψ (Formalism.L2.DIV.actP lam g F) = MvPolynomial.eval (fun v : (ι ⊕ ι) × Fin n × Fin n =>
      Sum.elim (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)
        (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.2 v.2.1) v.1) P := by
  intro K _ ι _ n lam F ψ
  refine ⟨detTwPoly lam * ∑ m ∈ (genSub F).support, (genSub F).coeff m * MvPolynomial.C (ψ (MvPolynomial.monomial m 1)), ?_⟩
  intro g
  rw [MvPolynomial.eval_mul, ← lin_map_eval]
  change ψ _ = MvPolynomial.eval (evPt g) (detTwPoly lam) * ψ (MvPolynomial.map (MvPolynomial.eval (evPt g)) (genSub F))
  rw [eval_detTwPoly, map_genSub]
  show ψ (Formalism.L2.DIV.detTwK lam g • Formalism.L2.DIV.trAct g F) = _
  rw [map_smul, smul_eq_mul]

end GlobalTheory.ActPolyCoeff

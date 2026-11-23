import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf

theorem mvZ_scal_monomial {ι : Type} {a b : ℕ} (r : ι → ℂ) (k : ι × Fin b × Fin a →₀ ℕ) (c : ℂ) :
    mvZ (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (fun τ => r τ • (1 : Matrix (Fin b) (Fin b) ℂ)) (MvPolynomial.monomial k c) =
      MvPolynomial.monomial k (c * k.prod fun v n => r v.1 ^ n) := by
  set M := mvZ (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (fun τ => r τ • (1 : Matrix (Fin b) (Fin b) ℂ)) with hM
  have hX : ∀ v : ι × Fin b × Fin a, M (MvPolynomial.X v) = MvPolynomial.C (r v.1) * MvPolynomial.X v := by
    intro v
    simp only [hM, mvZ, MvPolynomial.aeval_X]
    rw [Finset.sum_eq_single v.2.1]
    · rw [Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj; simp [Matrix.one_apply_ne (Ne.symm hj)]
      · simp
    · intro i _ hi; simp [Matrix.one_apply_ne hi]
    · simp
  have hC : M (MvPolynomial.C c) = MvPolynomial.C c := by
    simp only [hM, mvZ, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.monomial_eq, hC]
  simp only [Finsupp.prod, map_prod, map_pow, hX, mul_pow, Finset.prod_mul_distrib, MvPolynomial.C_mul, mul_assoc]

end GlobalTheory.KJInf

namespace GlobalTheory.KJInf

theorem jetP_eq_jetL : ∀ (D : D7) (S T : HSp D) (s : ℂ) (cD : D.what₂.Tau → ℂ), (∀ τ, cD τ ≠ 0) → ∀ (G : VCx D.what₂.Tau S.rank T.rank → ℂ) (P : FP D.what₂.Tau S.rank T.rank), jetP S T rfl rfl s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) P) := by
  intro D S T s cD hcD G P
  have hid : (fun v : FVar D T.rank S.rank => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; rfl
  unfold GlobalTheory.AdForm.jetP
  rw [hid]
  simp only [Finsupp.mapDomain_id]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mvZ_scal_monomial]
  have hm : ∀ x : ℂ, (MvPolynomial.monomial k x : FP D.what₂.Tau S.rank T.rank) = x • MvPolynomial.monomial k 1 := by
    intro x; rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, jetL_monomial, smul_eq_mul]
  unfold jetC
  rw [mul_assoc, ← mul_assoc (k.prod _), ← Finsupp.prod_mul]
  congr 2
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← mul_pow, div_mul_cancel₀ _ (hcD v.1)]

end GlobalTheory.KJInf

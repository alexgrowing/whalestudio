import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantPhiSolutionMemOEStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.EquivOE

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_dvd_E : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (X : Matrix (Fin d') (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) →
    bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) →
    ∀ i j, X i j ∈ bk.OE := by
  intro l _ K bk d d' S S' X hg hφ
  obtain ⟨u, hu, heu⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.1 bk.E (not_dvd_E bk)
  have hA : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, S.A_mul]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : X = (u ^ (S'.a + S.b) * bk.evW bk.E ^ S.a) •
      (S'.A.map bk.evW * X.map (frobW l) * S.A'.map bk.evW) := by
    rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm u, heu, one_pow, one_smul]
  intro i j
  refine GlobalTheory.T.mem_OE_of_invariant_frobenius_solution l K bk (Fin d' × Fin d) (fun p => X p.1 p.2)
    (fun p q => u ^ (S'.a + S.b) * bk.evW bk.E ^ S.a * bk.evW (S'.A q.1 p.1) * bk.evW (S.A' p.2 q.2))
    (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
  · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hu _) (bk.OE.pow_mem (evW_mem bk _) _))
      (evW_mem bk _)) (evW_mem bk _)
  · have h2 := congrFun (congrFun h1 q.1) q.2
    rw [h2, Fintype.sum_prod_type_right]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  · exact congrFun (congrFun (hg g h) q.1) q.2

end GlobalTheory.BSP.EquivOE

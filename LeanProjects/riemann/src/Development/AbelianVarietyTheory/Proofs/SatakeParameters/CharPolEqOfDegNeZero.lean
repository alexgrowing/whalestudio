import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEq
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem trace_eq_of_trace_mul_pow {n m : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (B T : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (h : ∀ i : ℕ, 1 ≤ i → (S * A ^ i).trace = (T * B ^ i).trace) : S.trace = T.trace := by
  set P := A.charpoly * B.charpoly with hP
  have hPA : Polynomial.aeval A P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hPB : Polynomial.aeval B P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, mul_zero]
  have eA := congrArg (fun M => (S * M).trace) hPA
  have eB := congrArg (fun M => (T * M).trace) hPB
  simp only [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, mul_zero, Matrix.trace_zero] at eA eB
  rw [Finset.sum_range_succ'] at eA eB
  have hs : ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (S * A ^ (i + 1)).trace =
      ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (T * B ^ (i + 1)).trace :=
    Finset.sum_congr rfl fun i _ => by rw [h (i + 1) (by omega)]
  rw [hs] at eA
  have e0 : P.coeff 0 * (S * A ^ 0).trace = P.coeff 0 * (T * B ^ 0).trace := by linear_combination eA - eB
  simp only [pow_zero, Matrix.mul_one] at e0
  have hc : P.coeff 0 ≠ 0 := by
    rw [hP, Polynomial.mul_coeff_zero]
    refine mul_ne_zero (fun h0 => hA.ne_zero ?_) (fun h0 => hB.ne_zero ?_)
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  exact mul_left_cancel₀ hc e0

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem charpoly_eq_toMatrix' {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    f.charpoly = (LinearMap.toMatrix' f).charpoly := by
  rw [← LinearMap.charpoly_toMatrix f (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']

theorem trace_eq_of_charpoly_eq {n : ℕ} {M M' : Matrix (Fin n) (Fin n) ℂ} (e : M.charpoly = M'.charpoly) :
    M.trace = M'.trace := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]

theorem charPol_eq_of_deg_ne_zero : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (x y : WD h), (∀ σ : Weil h, deg σ ≠ 0 → x.charPol σ = y.charPol σ) → ∀ σ : Weil h, x.charPol σ = y.charPol σ := by
  intro K Ω _ _ _ _ _ A v h x y hxy σ
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  simp only [WD.charPol_mk] at hxy ⊢
  have hnm : n = m := by
    have e := congrArg Polynomial.natDegree (hxy (frob h) (by rw [deg_frob]; exact one_ne_zero))
    rwa [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at e
  subst hnm
  by_cases hσ : deg σ = 0
  swap
  · exact hxy σ hσ

  have hMA : ∀ τ : Weil h, LinearMap.toMatrix' (a.ρ τ) = (a.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL a τ).symm
  have hMB : ∀ τ : Weil h, LinearMap.toMatrix' (b.ρ τ) = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL b τ).symm
  have hne : ∀ τ : Weil h, deg τ ≠ 0 →
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ hτ
    refine trace_eq_of_charpoly_eq ?_
    rw [← hMA, ← hMB, ← charpoly_eq_toMatrix', ← charpoly_eq_toMatrix']
    exact hxy τ hτ
  have hall : ∀ τ : Weil h,
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ
    by_cases hτ : deg τ = 0
    swap
    · exact hne τ hτ
    refine trace_eq_of_trace_mul_pow (a.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      (b.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      ((Matrix.isUnit_iff_isUnit_det _).1 (a.toGL (frob h)).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).1 (b.toGL (frob h)).isUnit) fun i hi => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
      ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    refine hne _ ?_
    rw [deg_mul, deg_pow, hτ, deg_frob]
    omega
  rw [charpoly_eq_toMatrix', charpoly_eq_toMatrix', hMA, hMB]
  refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun j => ?_
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  exact hall _

end GlobalTheory.AboveL

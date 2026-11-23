import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerAnalyticFOfCls
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet

open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ m, ⟪C (stdOrthonormalBasis ℂ Wq m), A (stdOrthonormalBasis ℂ Wq m)⟫_ℂ := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]

end HS

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2)
    (h1 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (X.t Y a b Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ)
    (h2 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(X.t (star Y) b a Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  have hA := Formalism.FourierDecayAlt.P.actual_adjointness Wp Wq P z z' π π' hP X μ hμ Φ Ψ c hc hK Y a b
  simp only [pairAt, hsInner_eq_sum]
  rw [integral_finsetSum _ (fun m _ => h1 m), integral_finsetSum _ (fun m _ => h2 m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e := congrArg (starRingEnd ℂ) (hA (stdOrthonormalBasis ℂ Wq m))
  rw [← integral_conj, ← integral_conj] at e
  simp only [inner_conj_symm] at e
  exact e

end Adj

end Formalism.FourierDecayAlt.P5.HerA

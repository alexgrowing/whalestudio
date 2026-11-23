import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

open UpperHalfPlane hiding I

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_eq_rhom {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = rhom x v := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem reAt_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x y : F) :
    reAt v (x * y) = reAt v x * reAt v y := by
  rw [reAt_eq_rhom, reAt_eq_rhom, reAt_eq_rhom, map_mul, Pi.mul_apply]

theorem sum_reAt_eq_trace {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ∑ v, (reAt v x : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have key : ∑ v : InfinitePlace F, reAt v x = ∑ σ : F →+* ℝ, σ x := by
    refine Fintype.sum_bijective (fun v => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      ⟨?_, ?_⟩ _ _ ?_
    · intro v w h
      have hvw : v.embedding = w.embedding := by
        ext y
        rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v),
          ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal w)]
        exact congrArg (fun f : F →+* ℝ => ((f y : ℝ) : ℂ)) h
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w, hvw]
    · intro φ
      have hψ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp φ) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        simp
      refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp φ), ?_⟩
      ext y
      apply Complex.ofReal_injective
      rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    · intro v
      exact reAt_eq_rhom v x
  rw [← Complex.ofReal_sum, key, ← trace_eq_sum_realEmbeddings, Complex.ofReal_ratCast]

theorem cmp_toInf_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) F)
    (v : InfinitePlace F) (i j : Fin 2) :
    ((cmp v (toInf g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = rhom ((g : Matrix (Fin 2) (Fin 2) F) i j) v := rfl

theorem denom_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℂ) :
    denom (cmp v (toInf (aff 1 b))) w = 1 := by
  simp [denom, cmp_toInf_apply, aff]

theorem coe_translate_smul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℍ) :
    ((cmp v (toInf (aff 1 b)) • w : ℍ) : ℂ) = (w : ℂ) + (reAt v b : ℂ) := by
  have e : ∀ i j, ((cmp v (toInf (aff 1 b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      rhom ((aff (1 : Fˣ) b : Matrix (Fin 2) (Fin 2) F) i j) v := fun i j => cmp_toInf_apply _ v i j
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff 1 b)))) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e, e, e, e]
    simp [aff]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, denom_translate]
  simp only [UpperHalfPlane.num, e]
  simp [aff, reAt_eq_rhom]

theorem ez_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b ξ : F) (z : Hn F) :
    ez ξ (act (toInf (aff 1 b)) z) = et (b * ξ) * ez ξ z := by
  rw [mul_comm b ξ]
  have h := sum_reAt_eq_trace (ξ * b)
  simp only [ez, et, act, coe_translate_smul]
  rw [← Complex.exp_add, ← h]
  congr 1
  simp only [reAt_mul, Complex.ofReal_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem th_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ),
    sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  intro F _ _ _ κ _ _ G k b Φ
  funext z
  simp only [sl0, denom_translate, Finset.prod_const_one, inv_one, one_pow, one_mul, th]
  refine tsum_congr fun x => ?_
  rw [ez_translate]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_translation_twists_coefficients : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ), sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_translate | exact GlobalTheory.HilbertThetaSeries.th_translate | (intros; apply GlobalTheory.HilbertThetaSeries.th_translate <;> assumption)

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.PassageScaleFree
import Formalism.QuotientMetricDivisors.FinalW

open Module NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef

noncomputable section
namespace GlobalTheory.RowSlopeProbe

section General
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem majAt_scale {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (v : InfinitePlace K) (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) (scaleFrame t X) v x y =
      (t v : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y := by
  have hs : ((Real.sqrt (t v) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (ht v)).ne'
  have hi : (scaleFrame t X v)⁻¹ = ((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp only [scaleFrame, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hX v)]
    rw [Complex.ofReal_inv]
    first | rw [mul_inv_cancel₀ hs, one_smul] | rw [inv_mul_cancel₀ hs, one_smul]
  have h2 : ((Real.sqrt (t v) : ℝ) : ℂ) * ((Real.sqrt (t v) : ℝ) : ℂ) = (t v : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ht v).le]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, hi, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, star_mul',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h2, Complex.star_def, Complex.conj_ofReal]
  ring

theorem scale_unit {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (v : InfinitePlace K) : IsUnit (scaleFrame t X v).det := by
  have hs : ((Real.sqrt (t v))⁻¹ : ℝ) ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (ht v)).ne'
  simp only [scaleFrame, Matrix.det_smul]
  exact (IsUnit.mk0 _ (pow_ne_zero _ (by exact_mod_cast hs))).mul (hX v)

def rescale (S : IndefRows Df) (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) : IndefRows Df where
  toIndefData := { S.toIndefData with
    XE := scaleFrame (fun v => ∏ _j : Bs.J, t v) S.XE
    XW := fun j => scaleFrame t (S.XW j)
    lam := fun j u p v => t v * S.lam j u p v }
  pos := S.pos
  proviso := S.proviso
  types := S.types
  h0 := S.h0
  frames := ⟨scale_unit _ S.frames.1 _ fun v => Finset.prod_pos fun _ _ => ht v,
    fun j => scale_unit _ (S.frames.2.1 j) _ ht, S.frames.2.2⟩
  l1a := S.l1a
  l1c := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := S.l1c
    refine ⟨h1, h2, h3, fun j u p v => mul_pos (ht v) (h4 j u p v), fun u v h p x hx y => ?_,
      fun j u v h p x hx y => ?_⟩
    · have := h5 u v h p x hx y
      show Formalism.HermitianLatticesTheory.majAt _ (scaleFrame _ S.XE) v _ _ = _
      rw [majAt_scale _ S.frames.1 _ (fun v => Finset.prod_pos fun _ _ => ht v), this]
      simp only [Finset.prod_mul_distrib]
      push_cast
      ring
    · have := h6 j u v h p x hx y
      show Formalism.HermitianLatticesTheory.majAt _ (scaleFrame _ (S.XW j)) v _ _ = _
      rw [majAt_scale _ (S.frames.2.1 j) _ ht, this]
      push_cast
      ring
  l1d := S.l1d

end General

section Concrete
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def resize (F : Face D A) (b' : ℝ) : Face D A :=
  { F with Zsc := fun Zs => { F.Zsc Zs with x := 1, b := b' } }

end Concrete

end GlobalTheory.RowSlopeProbe

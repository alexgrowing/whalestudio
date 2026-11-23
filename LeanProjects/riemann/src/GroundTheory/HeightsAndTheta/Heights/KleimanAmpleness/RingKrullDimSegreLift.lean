import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsRelevant)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable section

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type}

theorem segreLiftMap_segreIncl (W : Ideal (MRing ι F)) (s : MRing ι F) :
    segreLiftMap ι F W (segreIncl ι F s) = Polynomial.C (Ideal.Quotient.mk W s) := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (IsScalarTower.toAlgHom F (MRing ι F ⧸ W) (Polynomial (MRing ι F ⧸ W))).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [segreIncl, segreLiftMap, segreLiftVal]
  simpa using DFunLike.congr_fun h s

abbrev segreLiftAlgebra (W : Ideal (MRing ι F)) :
    Algebra (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) :=
  RingHom.toAlgebra' (Ideal.kerLiftAlg (segreLiftMap ι F W)).toRingHom
    fun c x => mul_comm ((Ideal.kerLiftAlg (segreLiftMap ι F W)).toRingHom c) x

theorem isAlgebraic_segreLift (W : Ideal (MRing ι F)) [W.IsPrime] (hrel : IsRelevant W) :
    letI := segreLiftAlgebra W
    Algebra.IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) := by
  classical
  let _ := segreLiftAlgebra W
  have : (RingHom.ker (segreLiftMap ι F W)).IsPrime := RingHom.ker_isPrime _
  have hmap : ∀ x, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ x) = segreLiftMap ι F W x :=
    fun x => Ideal.kerLiftAlg_mk (segreLiftMap ι F W) x
  choose c hc using hrel
  have hm : Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩ : MRing ι F) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.IsPrime.prod_mem_iff]
    simpa using hc
  have hC : ∀ s : MRing ι F, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreIncl ι F s)) =
        Polynomial.C (Ideal.Quotient.mk W s) := fun s => by
    rw [hmap, segreLiftMap_segreIncl]
  have hY : algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreY c)) =
        Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩)) := by
    rw [hmap]
    simp [segreLiftMap, segreY, segreLiftVal]
  have hX : IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial.X : Polynomial (MRing ι F ⧸ W)) := by
    refine ⟨Polynomial.C (Ideal.Quotient.mk _ (segreIncl ι F (∏ k, X ⟨k, c k⟩))) * Polynomial.X -
      Polynomial.C (Ideal.Quotient.mk _ (segreY c)), ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun p => algebraMap
        (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
        (Polynomial (MRing ι F ⧸ W)) (Polynomial.coeff p 1)) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_true, one_ne_zero, if_false, sub_zero, Polynomial.coeff_zero, map_zero, hC,
        Polynomial.C_eq_zero] at h1
      exact hm h1
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, hC, hY]
      ring
  refine ⟨fun p => ?_⟩
  have : p ∈ Subalgebra.algebraicClosure (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) := by
    rw [p.as_sum_range_C_mul_X_pow]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (p.coeff i)
    rw [← hs, ← hC]
    exact isAlgebraic_algebraMap _
  exact this

open Algebra in

theorem ringKrullDim_segreLift [∀ k, Fintype (ι k)] [DecidableEq K] (W : Ideal (MRing ι F))
    [W.IsPrime] (hrel : IsRelevant W) :
    ringKrullDim (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) =
      ringKrullDim (MRing ι F ⧸ W) + 1 := by
  let _ : ∀ x, Fintype (segreIdx ι x) := fun x => match x with
    | .inl _ => (inferInstance : Fintype (∀ k, ι k))
    | .inr k => (inferInstance : Fintype (ι k))
  let _ := segreLiftAlgebra W
  have : (RingHom.ker (segreLiftMap ι F W)).IsPrime := RingHom.ker_isPrime _
  have : IsScalarTower F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((Ideal.kerLiftAlg (segreLiftMap ι F W)).commutes c).symm
  have : FaithfulSMul (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)
  have := isAlgebraic_segreLift W hrel
  obtain ⟨n, hA, htA⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)
  have hP : trdeg F (Polynomial (MRing ι F ⧸ W)) = n + 1 := by
    rw [← trdeg_add_eq F (MRing ι F ⧸ W) (A := Polynomial (MRing ι F ⧸ W)),
      Polynomial.trdeg_of_isDomain, htA]
  have hQ : trdeg F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) = n + 1 := by
    have h2 := trdeg_add_eq F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (A := Polynomial (MRing ι F ⧸ W))
    rw [trdeg_eq_zero (R := MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (A := Polynomial (MRing ι F ⧸ W)), add_zero] at h2
    rw [h2, hP]
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hQ, hA]
  simp

theorem SegreLiftRelDim.proof : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  have h := ringKrullDim_segreLift W hW.relevant
  obtain ⟨n, hA, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)
  unfold relDim
  erw [h, hA]
  rw [show ((n : WithBot ℕ∞) + 1) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast,
    show (n : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast]
  simp only [WithBot.map_coe, Fintype.card_sum, Fintype.card_unit]
  congr 1
  change WithTop.map _ (WithTop.some (n + 1)) = WithTop.map _ (WithTop.some n)
  rw [WithTop.map_coe, WithTop.map_coe]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQuaStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitVacSum

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem idem_trace_det (P : Matrix ι ι ℂ) (hP : P * P = P) :
    P.trace = P.rank ∧ ∀ u : ℂ, (u • P + (1 - P)).det = u ^ P.rank := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) :=
    LinearMap.IsIdempotentElem.isProj_range _ hi
  have hr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = P.rank := rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← Matrix.trace_toLin'_eq, hp.trace, hr]
  · rw [← LinearMap.det_toLin']
    have e := hp.eq_conj_prodMap
    set c := (Submodule.prodEquivOfIsCompl _ _ hp.isCompl)
    have e2 : Matrix.toLin' (u • P + (1 - P)) = c.conj (LinearMap.prodMap (u • LinearMap.id) LinearMap.id) := by
      have : LinearMap.prodMap (u • LinearMap.id) LinearMap.id =
          u • LinearMap.prodMap (LinearMap.id : LinearMap.range (Matrix.toLin' P) →ₗ[ℂ] _) (0 : LinearMap.ker (Matrix.toLin' P) →ₗ[ℂ] _)
            + (1 - LinearMap.prodMap LinearMap.id 0) := by
        refine LinearMap.ext fun x => ?_
        ext <;> simp
      rw [this, map_add, map_add, map_smul, map_smul, map_sub, map_sub, ← e, Matrix.toLin'_one]
      congr 2
      exact (LinearEquiv.conj_id c).symm
    rw [e2, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
      LinearMap.det_id, LinearMap.det_id, hr, mul_one, mul_one]

theorem half_idem {s : Matrix ι ι ℂ} (hs : s * s = 1) :
    ((1 / 2 : ℂ) • (1 + s)) * ((1 / 2 : ℂ) • (1 + s)) = (1 / 2 : ℂ) • (1 + s) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, mul_add, add_mul, hs, mul_one, one_mul]
  module

theorem le_rank_half {m : ℕ} {G s t : Matrix ι ι ℂ} (hpos : (G * s).PosDef) (ht : t = s ∨ t = -s)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) :
    m ≤ ((1 / 2 : ℂ) • (1 + t)).rank := by
  refine le_trans ?_ (Matrix.rank_mul_le_left _ B)
  have hinj : Function.Injective (((1 / 2 : ℂ) • (1 + t)) * B).mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : B *ᵥ a + t *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at ha
      exact (smul_eq_zero.1 ha).resolve_left (by norm_num)
    have h2 : star (B *ᵥ a) ⬝ᵥ G *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
        Matrix.zero_mulVec, dotProduct_zero]
    have h3 : star (B *ᵥ a) ⬝ᵥ (G * s) *ᵥ (B *ᵥ a) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      rcases ht with rfl | rfl
      · rw [eq_neg_of_add_eq_zero_right h1, Matrix.mulVec_neg, dotProduct_neg, h2, neg_zero]
      · rw [Matrix.neg_mulVec, add_neg_eq_zero] at h1
        rw [← h1, h2]
    have h4 : B *ᵥ a = 0 := by
      by_contra h
      exact (hpos.dotProduct_mulVec_pos h).ne' h3
    rw [← Matrix.one_mulVec a, ← hC, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  unfold Matrix.rank
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

theorem trace_eq_zero {m : ℕ} {G s : Matrix ι ι ℂ} (hs : s * s = 1) (hpos : (G * s).PosDef) (hm : 2 * m = Fintype.card ι)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) : s.trace = 0 := by
  have a1 := le_rank_half hpos (Or.inl rfl) B C hC hB
  have a2 := le_rank_half hpos (Or.inr rfl) B C hC hB
  have b1 := (idem_trace_det _ (half_idem hs)).1
  have b2 := (idem_trace_det _ (half_idem (s := -s) (by rw [neg_mul_neg, hs]))).1
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, ← hm, smul_eq_mul] at b1 b2
  rw [Matrix.trace_neg] at b2
  have c : ((((1 / 2 : ℂ) • (1 + s)).rank + ((1 / 2 : ℂ) • (1 + -s)).rank : ℕ) : ℂ) = (2 * m : ℕ) := by
    rw [Nat.cast_add, ← b1, ← b2]; ring
  have c' := Nat.cast_injective c
  have d : ((1 / 2 : ℂ) • (1 + s)).rank = m := by omega
  rw [d] at b1
  push_cast at b1
  linear_combination 2 * b1

end Lin

theorem detPlus_one {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus sS sT ((1 : ℂ) • 1) ((1 : ℂ) • 1) = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  rw [one_smul, one_smul, Matrix.transpose_one, Matrix.one_kronecker_one, mul_one,
    show (1 / 2 : ℂ) • (1 + sT ⊗ₖ sSᵀ) + (1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ) = 1 by module, Matrix.det_one]

variable {D : D7} {θ : InfFam D}

end GlobalTheory.SplitVacSum

end

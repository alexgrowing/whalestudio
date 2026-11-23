import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationAdicCompletion
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivationMemPowOfMemPowSucc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion

variable {R : Type} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R)

theorem derivation_mem_pow_of_mem_pow_succ {n : ℕ} {r : R} (hr : r ∈ I ^ (n + 1)) : D r ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ <;> assumption

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal R) = I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

noncomputable def derivQuot (n : ℕ) :
    R ⧸ (I ^ (n + 1) • ⊤ : Ideal R) →+ R ⧸ (I ^ n • ⊤ : Ideal R) :=
  QuotientAddGroup.lift (I ^ (n + 1) • ⊤ : Ideal R).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R)).toAddMonoidHom.comp (D : R →ₗ[ℤ] R).toAddMonoidHom)
    (fun r hr => by
      change r ∈ (I ^ (n + 1) • ⊤ : Ideal R) at hr
      rw [AddMonoidHom.mem_ker]
      change Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_smul_top_eq]
      rw [pow_smul_top_eq] at hr
      exact derivation_mem_pow_of_mem_pow_succ I D hr)

theorem derivQuot_mk (n : ℕ) (r : R) :
    derivQuot I D n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) := rfl

theorem exists_rep_succ (x : AdicCompletion I R) (n : ℕ) :
    ∃ a : R, x.val (n + 1) = Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a ∧
      x.val n = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
  refine ⟨a, ha.symm, ?_⟩
  rw [← x.property (Nat.le_succ n), ← ha]
  rfl

noncomputable def derivCompletionAdd : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n => derivQuot I D n (x.val (n + 1)), fun {m n} hmn => by
    change transitionMap I R hmn (derivQuot I D n (x.val (n + 1))) = derivQuot I D m (x.val (m + 1))
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
    have hm : x.val (m + 1) = Ideal.Quotient.mk (I ^ (m + 1) • ⊤ : Ideal R) a := by
      rw [← x.property (Nat.succ_le_succ hmn), ← ha]
      rfl
    rw [hm, ← ha, derivQuot_mk, derivQuot_mk]
    rfl⟩
  map_zero' := AdicCompletion.ext fun n => map_zero (derivQuot I D n)
  map_add' x y := AdicCompletion.ext fun n => map_add (derivQuot I D n) _ _

noncomputable def derivCompletion : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (derivCompletionAdd I D).toIntLinearMap (fun a b => by
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨p, hp1, hp0⟩ := exists_rep_succ I a n
    obtain ⟨q, hq1, hq0⟩ := exists_rep_succ I b n
    change derivQuot I D n ((a * b).val (n + 1)) =
      a.val n * derivQuot I D n (b.val (n + 1)) + b.val n * derivQuot I D n (a.val (n + 1))
    rw [val_mul, hp1, hq1, hp0, hq0, ← map_mul, derivQuot_mk, derivQuot_mk, derivQuot_mk, D.leibniz,
      smul_eq_mul (α := R), smul_eq_mul (α := R), map_add, map_mul, map_mul])

theorem DerivationAdicCompletion.proof : DerivationAdicCompletion.Statement := by
  intro R _ I D
  refine ⟨derivCompletion I D, fun r => AdicCompletion.ext fun n => ?_⟩
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

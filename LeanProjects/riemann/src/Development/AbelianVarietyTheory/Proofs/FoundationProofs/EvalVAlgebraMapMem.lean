import Mathlib
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemPrime

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem isIntegral_star {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd D.host.E) hx

theorem evalV_algebraMap_mem (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.F) (ht : IsIntegral ℤ t) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) t) ∈ v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes]
  have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) t) = v.valuation D.host.F t :=
    v.valuedAdicCompletion_eq_valuation' _
  show Valued.v (algebraMap D.host.F (Fv D.host.F v) t) ≤ 1
  rw [h2]
  exact v.valuation_le_one (K := D.host.F) (⟨t, ht⟩ : 𝓞 D.host.F)

theorem exists_trace {z : Formalism.L2.Theta.AE D} (hz : z ∈ intL D) :
    ∃ β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, z + cA D z = fj D β := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    obtain ⟨t, ht⟩ := exists_of_star_eq D (x := (o : D.host.E) + star (o : D.host.E))
      (by rw [star_add, star_star, add_comm])
    have hti : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective, ht]
      exact o.2.add (isIntegral_star o.2)
    refine ⟨algebraMap D.host.F (Af D.host.F) t * α, fun v => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (evalV_algebraMap_mem v t hti) (hα v)
    · rw [cA_tmul, ← TensorProduct.tmul_add, ← ht, tmul_algebraMap_eq, fj_eq]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [map_zero, map_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a + b, fun v => by rw [map_add]; exact add_mem (ha v) (hb v), by
      rw [RingHom.map_add, map_add (fj D), ← h1, ← h2, add_add_add_comm]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, h1⟩ := hx
    exact ⟨-a, fun v => by rw [map_neg]; exact neg_mem (ha v), by
      rw [RingHom.map_neg, map_neg (fj D), ← h1, neg_add]⟩

theorem finPart_mem {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])

theorem mem_iff {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (y : Fv D.host.F v) :
    finPart D (fj D (singleV D.host.F v y) * e) ∈ intAE D ↔ Valued.v y ≤ 1 := by
  constructor
  · intro h
    have h1 := inF_mem h
    rw [inF_finPart, ← mul_assoc, ← map_mul, one_mul] at h1
    obtain ⟨β, hβ, h2⟩ := exists_trace h1
    rw [map_mul, cA_fj, ← mul_add, he.2.2, ← map_mul] at h2
    have h3 := congrArg (evalV D.host.F v) (fj_inj D h2)
    rw [map_mul, evalV_singleV_same, evalV_singleV_same, mul_one] at h3
    rw [h3]
    exact hβ v
  · intro h
    rw [RingHom.map_mul]
    exact mul_mem_int (AddSubgroup.subset_closure
      ⟨singleV D.host.F v y, singleV_mem_intAf D.host.F v ⟨y, h⟩, 1, rfl⟩) (finPart_mem he)

theorem singleV_add (v : HeightOneSpectrum (𝓞 D.host.F)) (x y : Fv D.host.F v) :
    singleV D.host.F v (x + y) = singleV D.host.F v x + singleV D.host.F v y := by
  rw [← sub_eq_iff_eq_add, ← singleV_sub, add_sub_cancel_right]

theorem scalar_eq {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {a b : Fv D.host.F v}
    (h : fj D (singleV D.host.F v a) * e = fj D (singleV D.host.F v b) * e) : a = b := by
  have := he.scalar_inj h
  rwa [evalV_singleV_same, evalV_singleV_same] at this

theorem exists_hom {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) :
    ∃ φ : D.host.E →+* Fv D.host.F v, ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e := by
  choose f hf using fun x => he.exists_scalar (incA D x)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := fun x y => ?_, map_zero' := ?_, map_add' := fun x y => ?_ }, hf⟩
  · refine scalar_eq he ?_
    rw [← hf, map_one, mul_one, he.pl_mul]
  · refine scalar_eq he ?_
    have h : singleV D.host.F v (f x * f y) = singleV D.host.F v (f x) * singleV D.host.F v (f y) := by
      rw [singleV_mul, evalV_singleV_same]
    rw [← hf, map_mul, h, map_mul, ← mul_assoc, hf, mul_assoc, hf, mul_assoc]
  · refine scalar_eq he ?_
    rw [← hf, map_zero, mul_zero, ← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self, map_zero, zero_mul]
  · refine scalar_eq he ?_
    rw [← hf, map_add, singleV_add, map_add, mul_add, add_mul, hf, hf]

theorem hom_algebraMap {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {φ : D.host.E →+* Fv D.host.F v}
    (hφ : ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e) (t : D.host.F) :
    φ (algebraMap D.host.F D.host.E t) = algebraMap D.host.F (Fv D.host.F v) t := by
  refine scalar_eq he ?_
  have h1 : incA D (algebraMap D.host.F D.host.E t) =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (algebraMap D.host.F (AF D.host.F) t * 1) :=
    tmul_algebraMap_eq (1 : AF D.host.F) t
  have h2 : evalV D.host.F v (algebraMap D.host.F (AF D.host.F) t * 1).2 * 1 =
      algebraMap D.host.F (Fv D.host.F v) t := by
    rw [mul_one, mul_one]
    exact (evalV D.host.F v).commutes t
  rw [← hφ, h1, ← h2, ← singleV_mul, ← algebraMap_mul_fj, mul_assoc, he.pl_mul, mul_comm]

theorem exists_isIdemAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : Formalism.L2.Theta.AE D), GlobalTheory.IdemModTwo.SplitAt D v e → ∃ PP : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
  intro D v e he
  obtain ⟨φ, hφ⟩ := exists_hom he
  have hint : ∀ x : 𝓞 D.host.E, Valued.v (φ x) ≤ 1 := fun x => by
    rw [← mem_iff he, ← hφ, RingHom.map_mul]
    exact mul_mem_int (finPart_mem he) (AddSubgroup.subset_closure
      ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩)
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {x | Valued.v (φ x) < 1}
      add_mem' := fun {a b} ha hb => by
        show Valued.v (φ ((a : D.host.E) + b)) < 1
        rw [map_add]
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        show Valued.v (φ 0) < 1
        rw [map_zero, map_zero]; exact zero_lt_one
      smul_mem' := fun c x hx => by
        show Valued.v (φ ((c : D.host.E) * x)) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hI : ∀ x, x ∈ I ↔ Valued.v (φ x) < 1 := fun x => Iff.rfl
  have hcomap : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
    ext t
    rw [Ideal.mem_comap, hI]
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) := rfl
    have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) (algebraMap (𝓞 D.host.F) D.host.F t)) =
        v.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F t) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [h1, hom_algebraMap he hφ, h2]
    exact v.valuation_lt_one_iff_mem _
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : 𝓞 D.host.E) ∈ I := by rw [h]; trivial
      have h2 : Valued.v (φ 1) < 1 := h1
      rw [map_one, map_one] at h2
      exact lt_irrefl _ h2
    · have h2 : Valued.v (φ ((a : D.host.E) * b)) < 1 := hab
      rw [map_mul, map_mul] at h2
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h2 (not_lt.2 (one_le_mul hn.1 hn.2))
  have hne : I ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hcomap, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  refine ⟨⟨I, hprime, hne⟩, ⟨(isSplitIdem_iff e).2 ⟨v, he⟩, fun x hx => ?_⟩, hcomap⟩
  have hx0 : Valued.v (φ x) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]
    exact fun h => hx (Subtype.ext h)
  show x ∈ I ↔ _
  rw [hI, hφ, mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

end GlobalTheory.IdemPrime

end

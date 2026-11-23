import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.OrderTwoTate
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.EulerCharDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

namespace Involution

variable {M : Type*} [AddCommGroup M] {σ : M →+ M}

theorem ker_id_add_eq_fixedSub_neg : (AddMonoidHom.id M + σ).ker = fixedSub (-σ) := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_fixedSub, AddMonoidHom.add_apply, AddMonoidHom.id_apply,
    AddMonoidHom.neg_apply, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]

theorem card_tateQuot_mul_card (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot σ) * Nat.card M = Nat.card (fixedSub σ) * Nat.card (fixedSub (-σ)) := by
  have h1 : Nat.card (fixedSub σ) =
      Nat.card (tateQuot σ) * Nat.card (traceSub σ) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      ((traceSub σ).addSubgroupOf (fixedSub σ)),
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (traceSub_le_fixedSub hσ)).toEquiv]
  have h2 : Nat.card (traceSub σ) * Nat.card (fixedSub (-σ)) = Nat.card M := by
    rw [← ker_id_add_eq_fixedSub_neg, traceSub]
    rw [← AddSubgroup.index_ker, mul_comm, AddSubgroup.card_mul_index]
  rw [h1, mul_assoc, h2]

variable [Finite M]

theorem card_tateQuot_neg (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (tateQuot (-σ)) = Nat.card (tateQuot σ) := by
  have hσ' : ∀ x, (-σ) ((-σ) x) = x := fun x => by
    rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, map_neg, neg_neg, hσ]
  have e1 := card_tateQuot_mul_card hσ
  have e2 := card_tateQuot_mul_card hσ'
  rw [neg_neg, mul_comm (Nat.card (fixedSub (-σ)))] at e2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e2.trans e1.symm)

end Involution

namespace OrderTwo

section Card

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsDiscreteRep A] in
include hG hc in

theorem act_act (x : A) : act A c (act A c x) = x := by
  change A.ρ c (A.ρ c x) = x
  rw [← Module.End.mul_apply, ← map_mul, mul_self_eq_one hG hc, map_one, Module.End.one_apply]

variable [Finite A]

include hG hc in

theorem finite_cohomology_one : Finite (cohomology A 1) :=
  Finite.of_equiv _ (h1EquivOfOrderTwo A hG hc).toEquiv

include hG hc in

theorem finite_cohomology_two : Finite (cohomology A 2) :=
  Finite.of_equiv _ (h2EquivOfOrderTwo A hG hc).toEquiv

include hG hc in

theorem card_cohomology_one_eq_two : Nat.card (cohomology A 1) = Nat.card (cohomology A 2) := by
  rw [← Nat.card_congr (h1EquivOfOrderTwo A hG hc).toEquiv, ← Nat.card_congr (h2EquivOfOrderTwo A hG hc).toEquiv]
  exact Involution.card_tateQuot_neg (act_act A hG hc)

include hG hc in

theorem eulerChar_eq_card_cohomology_zero : eulerChar A = Nat.card (cohomology A 0) := by
  have := finite_cohomology_one A hG hc
  have h1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := cohomology A 1)).ne'
  rw [eulerChar, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one,
    ← card_cohomology_one_eq_two A hG hc]
  norm_num
  field_simp

end Card

end OrderTwo

section RealPlace

open NumberField GroundTheory.Global

variable {K : FiniteSubfield} (v : InfinitePlace K.1) (hv : v.IsReal)
  (M : Rep.{0} (ULift.{0} ℤ) Gal(AlgebraicClosure v.Completion / v.Completion)) [IsDiscreteRep M]
  [Finite M]

include hv in

theorem card_cohomology_one_eq_two_of_isReal :
    Nat.card (cohomology M 1) = Nat.card (cohomology M 2) :=
  OrderTwo.card_cohomology_one_eq_two M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)

include hv in

theorem eulerChar_eq_card_cohomology_zero_of_isReal :
    eulerChar M = Nat.card (cohomology M 0) :=
  OrderTwo.eulerChar_eq_card_cohomology_zero M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)

include hv in

theorem finite_cohomology_of_isReal (n : ℕ) (hn : n ≤ 2) : Finite (cohomology M n) := by
  interval_cases n
  · exact Finite.of_equiv _ (H0Iso M).toLinearEquiv.toEquiv.symm
  · exact OrderTwo.finite_cohomology_one M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)
  · exact OrderTwo.finite_cohomology_two M (eq_one_or_eq_realConj v hv) (realConj_ne_one v hv)

end RealPlace

section GS

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (v : {v : InfinitePlace K.1 // v.IsReal})

instance finite_res_gsRealFamily : Finite (Rep.res (gsRealFamily S ιr v).toMonoidHom M) :=
  inferInstanceAs (Finite M)

theorem gsReal_card_cohomology_one_eq_two :
    Nat.card (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 1) =
      Nat.card (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 2) :=
  card_cohomology_one_eq_two_of_isReal v.1 v.2 _

theorem gsReal_eulerChar_eq_card_cohomology_zero :
    eulerChar (Rep.res (gsRealFamily S ιr v).toMonoidHom M) =
      Nat.card (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) :=
  eulerChar_eq_card_cohomology_zero_of_isReal v.1 v.2 _

theorem gsReal_finite_cohomology (n : ℕ) (hn : n ≤ 2) :
    Finite (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) n) :=
  finite_cohomology_of_isReal v.1 v.2 _ n hn

end GS

end GroundTheory.ProfCoh

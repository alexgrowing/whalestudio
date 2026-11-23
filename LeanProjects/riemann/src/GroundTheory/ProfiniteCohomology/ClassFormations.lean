import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormationDefs
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.ClassFormations.Quotient
import GroundTheory.ProfiniteCohomology.ClassFormations.Finite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section QuotQuot

variable {U V V' : Subgroup G} [(V.subgroupOf U).Normal] [(V'.subgroupOf U).Normal]

def quotQuotHom (h : V' ≤ V) : U ⧸ V'.subgroupOf U →* U ⧸ V.subgroupOf U :=
  QuotientGroup.map _ _ (MonoidHom.id U) fun _ hx => h hx

omit [IsTopologicalGroup G] in
theorem continuous_quotQuotHom (h : V' ≤ V) : Continuous (quotQuotHom (U := U) h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 QuotientGroup.continuous_mk

variable (C : Rep.{u} k G)

noncomputable def quotQuotRepHom (h : V' ≤ V) :
    Rep.res (quotQuotHom (U := U) h)
        ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U)) ⟶
      (Rep.res U.subtype C).quotientToInvariants (V'.subgroupOf U) :=
  Rep.ofHom
    { toFun := fun m => ⟨m.1, fun n => m.2 ⟨n.1, h n.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun x => by
        induction x using QuotientGroup.induction_on
        rfl }

variable [IsDiscreteRep C]

noncomputable def cohomologyInflQuotQuot (h : V' ≤ V) (n : ℕ) :
    cohomology ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U)) n ⟶
      cohomology ((Rep.res U.subtype C).quotientToInvariants (V'.subgroupOf U)) n :=
  cohomologyMapAlong (quotQuotHom h) (continuous_quotQuotHom h) (quotQuotRepHom C h) n

end QuotQuot

namespace PreClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

end PreClassFormation

namespace ClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem inv_injective (W : OpenSubgroup G) : Function.Injective (F.inv W) :=
  (F.inv_bijective W).1

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem exists_inv_eq (W : OpenSubgroup G) (q : QZ) : ∃ x : H2Open C W, F.inv W x = q :=
  (F.inv_bijective W).2 q

include hVU in

theorem tate_hypotheses (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V) :=
  F.toPreClassFormation.tate_hypotheses hVU F.inv_injective (F.exists_inv_eq U _) S

end ClassFormation

namespace ClassFormationAt

variable [CompactSpace G] [TotallyDisconnectedSpace G] {P : Set Nat.Primes}
  {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormationAt P C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem exists_inv_eq_one_div (W : OpenSubgroup G) {n : ℕ} (hn : n ≠ 0)
    (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∈ P) :
    ∃ x : H2Open C W, F.inv W x = QZ.mk (1 / (n : ℚ)) :=
  (AddMonoidHom.mem_range).1 (QZ.mem_of_nsmul_eq_zero P (F.inv W).range
    (F.primaryComponent_le_range W) n hn hP _ (QZ.nsmul_mk_one_div n))

variable (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ (V : Subgroup G).relIndex U → p ∈ P)

include hVU hP in

theorem tate_hypotheses (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V) :=
  F.toPreClassFormation.tate_hypotheses hVU F.inv_injective
    (F.exists_inv_eq_one_div U (relIndex_ne_zero_of_isOpen V.isOpen _) hP) S

end ClassFormationAt

end GroundTheory.ProfCoh

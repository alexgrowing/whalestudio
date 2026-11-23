import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

namespace QZ

theorem mem_of_nsmul_eq_zero (P : Set Nat.Primes) (H : AddSubgroup QZ)
    (hH : ∀ p ∈ P, ∀ x ∈ AddCommMonoid.primaryComponent QZ (p : ℕ), x ∈ H) :
    ∀ (n : ℕ), n ≠ 0 → (∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∈ P) →
      ∀ x : QZ, n • x = 0 → x ∈ H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hP x hx
    rcases eq_or_ne n 1 with rfl | h1
    · rw [one_smul] at hx
      rw [hx]
      exact H.zero_mem
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hnm
        exact hn hnm
      have ha : 0 < a := by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [pow_zero, one_mul] at hnm
          exact absurd (hnm ▸ Nat.minFac_dvd n) hpm
        · exact ha
      have hcop : Nat.Coprime (p ^ a) m :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)

      have hbez := Nat.gcd_eq_gcd_ab (p ^ a) m
      rw [hcop.gcd_eq_one] at hbez
      have hx' : x = ((p ^ a : ℕ) * Nat.gcdA (p ^ a) m : ℤ) • x +
          ((m : ℕ) * Nat.gcdB (p ^ a) m : ℤ) • x := by
        rw [← add_smul, ← hbez]
        simp
      rw [hx']
      refine H.add_mem ?_ ?_
      ·
        have hmn : m < n := by
          rw [hnm]
          calc m = 1 * m := (one_mul m).symm
            _ < p ^ a * m := by
              apply Nat.mul_lt_mul_of_pos_right _ (Nat.pos_of_ne_zero hm0)
              exact Nat.one_lt_pow ha.ne' hp.one_lt
        refine ih m hmn hm0 (fun q hq => hP q (hnm ▸ Dvd.dvd.mul_left hq _)) _ ?_
        rw [← natCast_zsmul, smul_smul]
        have : ((m : ℤ) * ((p ^ a : ℕ) * Nat.gcdA (p ^ a) m : ℤ)) =
            (Nat.gcdA (p ^ a) m) * (n : ℤ) := by
          rw [hnm]
          push_cast
          ring
        rw [this, ← smul_smul, natCast_zsmul, hx, smul_zero]
      ·
        have hpP : (⟨p, hp⟩ : Nat.Primes) ∈ P := hP ⟨p, hp⟩ (Nat.minFac_dvd n)
        refine hH _ hpP _ ⟨a, ?_⟩
        change (p : ℕ) ^ a • _ = 0
        rw [← natCast_zsmul, smul_smul]
        have : ((p ^ a : ℕ) : ℤ) * ((m : ℕ) * Nat.gcdB (p ^ a) m : ℤ) =
            (Nat.gcdB (p ^ a) m) * (n : ℤ) := by
          rw [hnm]
          push_cast
          ring
        rw [Nat.cast_pow] at this ⊢
        rw [this, ← smul_smul, natCast_zsmul, hx, smul_zero]

end QZ

variable {k G : Type u} [CommRing k] [Group G]

section Preimage

variable (U V : Subgroup G) [(V.subgroupOf U).Normal]

def quotPreimage (S : Subgroup (U ⧸ V.subgroupOf U)) : Subgroup G :=
  (S.comap (QuotientGroup.mk' (V.subgroupOf U))).map U.subtype

variable {U V}

theorem quotPreimage_le (S : Subgroup (U ⧸ V.subgroupOf U)) : quotPreimage U V S ≤ U :=
  Subgroup.map_subtype_le _

theorem mem_quotPreimage {S : Subgroup (U ⧸ V.subgroupOf U)} {g : G} (hg : g ∈ U) :
    g ∈ quotPreimage U V S ↔ ((⟨g, hg⟩ : U) : U ⧸ V.subgroupOf U) ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem le_quotPreimage (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    V ≤ quotPreimage U V S := by
  intro v hv
  rw [mem_quotPreimage (hVU hv), (QuotientGroup.eq_one_iff _).2 (by exact hv)]
  exact S.one_mem

def quotPreimageHom (S : Subgroup (U ⧸ V.subgroupOf U)) : quotPreimage U V S →* S :=
  ((QuotientGroup.mk' (V.subgroupOf U)).comp
    (Subgroup.inclusion (quotPreimage_le S))).codRestrict S fun w =>
      (mem_quotPreimage (quotPreimage_le S w.2)).1 w.2

@[simp]
theorem coe_quotPreimageHom_apply (S : Subgroup (U ⧸ V.subgroupOf U)) (w : quotPreimage U V S) :
    (quotPreimageHom S w : U ⧸ V.subgroupOf U) =
      ((⟨w.1, quotPreimage_le S w.2⟩ : U) : U ⧸ V.subgroupOf U) :=
  rfl

theorem quotPreimageHom_surjective (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Function.Surjective (quotPreimageHom S) := by
  rintro ⟨s, hs⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  exact ⟨⟨x.1, (mem_quotPreimage x.2).2 hs⟩, rfl⟩

theorem quotPreimageHom_eq_one_iff (S : Subgroup (U ⧸ V.subgroupOf U)) (w : quotPreimage U V S) :
    quotPreimageHom S w = 1 ↔ (w : G) ∈ V := by
  rw [← Subtype.coe_inj, coe_quotPreimageHom_apply, Subgroup.coe_one, QuotientGroup.eq_one_iff]
  exact Iff.rfl

theorem quotPreimageHom_ker (S : Subgroup (U ⧸ V.subgroupOf U)) :
    (quotPreimageHom S).ker = V.subgroupOf (quotPreimage U V S) := by
  ext w
  rw [MonoidHom.mem_ker, quotPreimageHom_eq_one_iff]
  exact Iff.rfl

theorem normal_subgroupOf_quotPreimage (S : Subgroup (U ⧸ V.subgroupOf U)) :
    (V.subgroupOf (quotPreimage U V S)).Normal := by
  rw [← quotPreimageHom_ker]
  exact MonoidHom.normal_ker _

attribute [instance] normal_subgroupOf_quotPreimage

noncomputable def quotPreimageEquiv (S : Subgroup (U ⧸ V.subgroupOf U)) :
    quotPreimage U V S ⧸ V.subgroupOf (quotPreimage U V S) ≃* S :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ (quotPreimageHom S) (quotPreimageHom_ker S).ge)
    ⟨(QuotientGroup.injective_lift_iff _ _ _).2 (quotPreimageHom_ker S).symm, by
      intro s
      obtain ⟨w, rfl⟩ := quotPreimageHom_surjective S s
      exact ⟨w, rfl⟩⟩

theorem relIndex_quotPreimage (S : Subgroup (U ⧸ V.subgroupOf U)) :
    V.relIndex (quotPreimage U V S) = Nat.card S := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_congr (quotPreimageEquiv S).toEquiv

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in

theorem continuous_quotPreimageHom (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Continuous (quotPreimageHom S) :=
  (QuotientGroup.continuous_mk.comp (continuous_subgroup_inclusion (quotPreimage_le S))).subtype_mk
    _

omit [IsTopologicalGroup G] in

theorem continuous_quotPreimageEquiv (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Continuous (quotPreimageEquiv S).toMonoidHom := by
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_quotPreimageHom S)

omit [IsTopologicalGroup G] in
theorem isOpen_subgroupOf {V : Subgroup G} (hV : IsOpen (V : Set G)) (W : Subgroup G) :
    IsOpen (V.subgroupOf W : Set W) :=
  hV.preimage continuous_subtype_val

omit [(V.subgroupOf U).Normal] in

theorem discreteTopology_quot (hV : IsOpen (V : Set G)) :
    DiscreteTopology (U ⧸ V.subgroupOf U) :=
  QuotientGroup.discreteTopology (isOpen_subgroupOf hV U)

theorem continuous_quotPreimageEquiv_symm (hV : IsOpen (V : Set G))
    (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Continuous (quotPreimageEquiv S).symm.toMonoidHom := by
  have := discreteTopology_quot (U := U) hV
  exact continuous_of_discreteTopology

end Preimage

section Cohomology

variable [TopologicalSpace G] [IsTopologicalGroup G] {U V : Subgroup G} [(V.subgroupOf U).Normal]
  (C : Rep.{u} k G) [IsDiscreteRep C]

instance isDiscreteRep_res_quotientToInvariants_res (S : Subgroup (U ⧸ V.subgroupOf U)) :
    IsDiscreteRep (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) :=
  isDiscreteRep_res_subtype _ _

noncomputable def quotPreimageRepHom (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Rep.res (quotPreimageHom S)
        (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) ⟶
      Rep.res (quotPreimage U V S).subtype C :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

noncomputable def cohomologyInflQuot (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    cohomology (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) n ⟶
      cohomology (Rep.res (quotPreimage U V S).subtype C) n :=
  cohomologyMapAlong (quotPreimageHom S) (continuous_quotPreimageHom S) (quotPreimageRepHom C S) n

@[reassoc]
theorem cohomologyRes_comp_cohomologyInflQuot (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    cohomologyRes ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U)) S n ≫
        cohomologyInflQuot C S n =
      cohomologyInfl (Rep.res U.subtype C) (V.subgroupOf U) n ≫
        cohomologyResLE C (quotPreimage_le S) n := by
  have : IsDiscreteRep (Rep.of (Rep.res U.subtype C).ρ) := isDiscreteRep_res_subtype C U
  rw [cohomologyRes, cohomologyInflQuot, ← cohomologyMapAlong_comp, cohomologyInfl,
    cohomologyResLE, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

noncomputable def quotPreimageInvHom (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Rep.res (quotPreimageEquiv S).toMonoidHom
        (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) ⟶
      (Rep.res (quotPreimage U V S).subtype C).quotientToInvariants
        (V.subgroupOf (quotPreimage U V S)) :=
  Rep.ofHom
    { toFun := fun m => ⟨m.1, fun n => m.2 ⟨⟨n.1.1, hVU n.2⟩, n.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun x => by
        induction x using QuotientGroup.induction_on
        rfl }

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep C] in
theorem quotPreimageInvHom_bijective (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Function.Bijective (quotPreimageInvHom C hVU S).hom := by
  refine ⟨fun a b h => ?_, fun c => ?_⟩
  · apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  refine ⟨⟨c.1, fun n => c.2 ⟨⟨n.1.1, le_quotPreimage hVU S n.2⟩, n.2⟩⟩, rfl⟩

theorem cohomologyInflQuot_eq (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    cohomologyInflQuot C S n =
      cohomologyMapAlong (quotPreimageEquiv S).toMonoidHom (continuous_quotPreimageEquiv S)
          (quotPreimageInvHom C hVU S) n ≫
        cohomologyInfl (Rep.res (quotPreimage U V S).subtype C)
          (V.subgroupOf (quotPreimage U V S)) n := by
  rw [cohomologyInfl, ← cohomologyMapAlong_comp, cohomologyInflQuot]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

theorem isIso_cohomologyMapAlong_quotPreimageEquiv (hV : IsOpen (V : Set G)) (hVU : V ≤ U)
    (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    IsIso (cohomologyMapAlong (quotPreimageEquiv S).toMonoidHom (continuous_quotPreimageEquiv S)
      (quotPreimageInvHom C hVU S) n) :=
  isIso_cohomologyMapAlong_of_mulEquiv _ _ (continuous_quotPreimageEquiv_symm hV S) _
    (quotPreimageInvHom_bijective C hVU S) n

end Cohomology

end GroundTheory.ProfCoh

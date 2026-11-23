import Mathlib
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.AdditiveHilbert
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits groupCohomology IntermediateField

universe u

section ULiftInt

def uliftIntLinearEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    A ≃ₗ[ULift.{u} ℤ] B :=
  { uliftIntLinearMap.{u} e.toAddMonoidHom with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

@[simp]
theorem uliftIntLinearEquiv_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (x : A) : uliftIntLinearEquiv.{u} e x = e x :=
  rfl

end ULiftInt

section Profinite

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem isZero_cohomology_of_forall_isZero (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ)
    (h : ∀ U : OpenNormalSubgroup G,
      IsZero (groupCohomology (A.quotientToInvariants (U : Subgroup G)) n)) :
    IsZero (cohomology A n) := by
  have hz : ∀ z : cohomology A n, z = 0 := fun z => by
    obtain ⟨U, w, rfl⟩ := exists_inflation_eq A n z
    have := ModuleCat.subsingleton_of_isZero (h U)
    rw [Subsingleton.elim w 0, map_zero]
  have : Subsingleton (cohomology A n) := ⟨fun x y => by rw [hz x, hz y]⟩
  exact ModuleCat.isZero_of_subsingleton _

end Profinite

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

section Additive

variable [IsGalois K L]

noncomputable def groupCohomologyQuotientGalAddIso (U : OpenNormalSubgroup Gal(L/K)) (n : ℕ) :
    groupCohomology ((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))) n ≅
      groupCohomology (galAdd K (fixedField (U : Subgroup Gal(L/K)))) n :=
  groupCohomology.mapIso (quotientEquivGal U) (invariantsGalAddEquiv U)
    (fun q => LinearMap.ext fun x => invariantsGalAddEquiv_quotientToInvariants U q x) n

theorem isZero_groupCohomology_quotientToInvariants_galAdd (U : OpenNormalSubgroup Gal(L/K))
    {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology ((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))) n) :=
  (isZero_groupCohomology_galois K (fixedField (U : Subgroup Gal(L/K))) hn).of_iso
    (groupCohomologyQuotientGalAddIso U n)

theorem isZero_cohomology_galAdd {n : ℕ} (hn : n ≠ 0) : IsZero (cohomology (galAdd K L) n) :=
  isZero_cohomology_of_forall_isZero _ n fun U =>
    isZero_groupCohomology_quotientToInvariants_galAdd U hn

theorem subsingleton_cohomology_galAdd {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (cohomology (galAdd K L) n) :=
  ModuleCat.subsingleton_of_isZero (isZero_cohomology_galAdd hn)

end Additive

section Units

variable (H : Subgroup Gal(L/K))

theorem mem_fixedField_of_mem_invariants_galUnits {v : Additive Lˣ}
    (hv : v ∈ Representation.invariants ((galUnits.{u} K L).ρ.comp H.subtype)) :
    ((Additive.toMul v : Lˣ) : L) ∈ fixedField H :=
  (mem_fixedField_iff _ _).2 fun σ hσ =>
    congrArg (fun w : Additive Lˣ => ((Additive.toMul w : Lˣ) : L)) (hv ⟨σ, hσ⟩)

noncomputable def invariantsGalUnitsAddEquiv :
    Representation.invariants ((galUnits.{u} K L).ρ.comp H.subtype) ≃+
      Additive (fixedField H)ˣ where
  toFun v := Additive.ofMul (Units.mk0 ⟨_, mem_fixedField_of_mem_invariants_galUnits H v.2⟩
    fun h => (Additive.toMul (α := Lˣ) v.1).ne_zero (congrArg Subtype.val h))
  invFun y := ⟨Additive.ofMul (Units.map ((algebraMap (fixedField H) L : _ →+* L) : _ →* L)
      (Additive.toMul y)), fun σ => Additive.toMul.injective (Units.ext
        ((mem_fixedField_iff _ _).1 ((Additive.toMul y : (fixedField H)ˣ) : fixedField H).2
          σ σ.2))⟩
  left_inv _ := Subtype.ext (Additive.toMul.injective (Units.ext rfl))
  right_inv _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  map_add' _ _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))

@[simp]
theorem coe_invariantsGalUnitsAddEquiv_apply
    (v : Representation.invariants ((galUnits.{u} K L).ρ.comp H.subtype)) :
    (((Additive.toMul (invariantsGalUnitsAddEquiv H v) : (fixedField H)ˣ) : fixedField H) : L) =
      ((Additive.toMul (α := Lˣ) v.1 : Lˣ) : L) :=
  rfl

variable [IsGalois K L]

theorem invariantsGalUnitsAddEquiv_quotientToInvariants (U : OpenNormalSubgroup Gal(L/K))
    (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (v : Representation.invariants ((galUnits.{u} K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsGalUnitsAddEquiv (U : Subgroup Gal(L/K))
        (((galUnits.{u} K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q v) =
      (galUnits.{u} K (fixedField (U : Subgroup Gal(L/K)))).ρ (quotientEquivGal U q)
        (invariantsGalUnitsAddEquiv (U : Subgroup Gal(L/K)) v) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    refine Additive.toMul.injective (Units.ext (Subtype.ext ?_))
    exact (quotientEquivGal_mk_apply U σ
      ⟨_, mem_fixedField_of_mem_invariants_galUnits (U : Subgroup Gal(L/K)) v.2⟩).symm

noncomputable def groupCohomologyQuotientGalUnitsIso (U : OpenNormalSubgroup Gal(L/K)) (n : ℕ) :
    groupCohomology ((galUnits.{u} K L).quotientToInvariants (U : Subgroup Gal(L/K))) n ≅
      groupCohomology (galUnits.{u} K (fixedField (U : Subgroup Gal(L/K)))) n :=
  groupCohomology.mapIso (quotientEquivGal U)
    (uliftIntLinearEquiv (invariantsGalUnitsAddEquiv (U : Subgroup Gal(L/K))))
    (fun q => LinearMap.ext fun v => invariantsGalUnitsAddEquiv_quotientToInvariants U q v) n

end Units

section Hilbert90

theorem isZero_groupCohomology_one_galUnits (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] : IsZero (groupCohomology (galUnits.{u} K E) 1) := by
  have hz : ∀ x : groupCohomology (galUnits.{u} K E) 1, x = 0 := fun x =>
    H1_induction_on x fun f => by
      rw [H1π_eq_zero_iff]
      have hf := (mem_cocycles₁_iff (A := galUnits.{u} K E) f).1 f.2
      obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
        (fun σ => Additive.toMul (α := Eˣ) (f σ)) fun g h =>
          congrArg (Additive.toMul (α := Eˣ)) (hf g h)
      exact ⟨Additive.ofMul β, funext fun σ => congrArg (Additive.ofMul (α := Eˣ)) (hβ σ)⟩
  have : Subsingleton (groupCohomology (galUnits.{u} K E) 1) := ⟨fun a b => by rw [hz a, hz b]⟩
  exact ModuleCat.isZero_of_subsingleton _

variable [IsGalois K L]

theorem isZero_groupCohomology_one_quotientToInvariants_galUnits
    (U : OpenNormalSubgroup Gal(L/K)) :
    IsZero (groupCohomology ((galUnits.{u} K L).quotientToInvariants (U : Subgroup Gal(L/K))) 1) :=
  (isZero_groupCohomology_one_galUnits K (fixedField (U : Subgroup Gal(L/K)))).of_iso
    (groupCohomologyQuotientGalUnitsIso U 1)

theorem isZero_cohomology_one_galUnits : IsZero (cohomology (galUnits.{u} K L) 1) :=
  isZero_cohomology_of_forall_isZero _ 1 isZero_groupCohomology_one_quotientToInvariants_galUnits

theorem subsingleton_cohomology_one_galUnits : Subsingleton (cohomology (galUnits.{u} K L) 1) :=
  ModuleCat.subsingleton_of_isZero isZero_cohomology_one_galUnits

end Hilbert90

section SeparableClosure

variable (K) (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

end SeparableClosure

end GroundTheory.ProfCoh

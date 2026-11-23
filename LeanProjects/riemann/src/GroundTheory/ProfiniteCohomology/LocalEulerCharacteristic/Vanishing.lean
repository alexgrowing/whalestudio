import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.VanishingCore
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.VanishingUnits
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Cohomology
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel IsLocalRing IntermediateField

section FixedField

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [ValuativeExtension K Ksep]

theorem isNonarchimedeanLocalField_fixedField (V : OpenSubgroup Gal(Ksep/K)) :
    letI := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
    IsNonarchimedeanLocalField (fixedField (V : Subgroup Gal(Ksep/K))) := by
  have hrel := valuativeRel_eq_finiteExtensionStructure K (L := fixedField (V : Subgroup Gal(Ksep/K)))
  have h1 := finiteExtensionStructure_isNonarchimedeanLocalField K (fixedField (V : Subgroup Gal(Ksep/K)))
  rw [← hrel] at h1
  exact h1

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in

theorem valuation_le_valuation_iff_coe (E : IntermediateField K Ksep) (x y : E) :
    valuation E x ≤ valuation E y ↔ valuation Ksep (x : Ksep) ≤ valuation Ksep (y : Ksep) := by
  rw [← (valuation E).vle_iff_le, ← (valuation Ksep).vle_iff_le, IntermediateField.coe_vle_coe_iff]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in
theorem valuation_le_one_iff_coe (E : IntermediateField K Ksep) (x : E) :
    valuation E x ≤ 1 ↔ valuation Ksep (x : Ksep) ≤ 1 := by
  rw [← map_one (valuation E), valuation_le_valuation_iff_coe, IntermediateField.coe_one, map_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in
theorem valuation_lt_one_iff_coe (E : IntermediateField K Ksep) (x : E) :
    valuation E x < 1 ↔ valuation Ksep (x : Ksep) < 1 := by
  rw [← not_le, ← not_le, ← map_one (valuation E), valuation_le_valuation_iff_coe,
    IntermediateField.coe_one, map_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in
theorem valuation_eq_iff_coe (E : IntermediateField K Ksep) (x y : E) :
    valuation E x = valuation E y ↔ valuation Ksep (x : Ksep) = valuation Ksep (y : Ksep) := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff_coe, valuation_le_valuation_iff_coe]

theorem natCast_residueField_fixedField_ne_zero {l : ℕ} (hl : (l : 𝓀[K]) ≠ 0)
    (V : OpenSubgroup Gal(Ksep/K)) :
    letI := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
    (l : 𝓀[fixedField (V : Subgroup Gal(Ksep/K))]) ≠ 0 := by
  let := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
  have := isNonarchimedeanLocalField_fixedField V
  have h := (algebraMap 𝓀[K] 𝓀[fixedField (V : Subgroup Gal(Ksep/K))]).injective.ne hl
  rwa [map_natCast, map_zero] at h

omit [IsSepClosure K Ksep] in

theorem natCast_ne_zero_of_residueField {l : ℕ} (hl : (l : 𝓀[K]) ≠ 0) : (l : K) ≠ 0 := by
  intro h
  apply hl
  have : ((l : 𝒪[K]) : K) = 0 := by push_cast; exact h
  have h0 : (l : 𝒪[K]) = 0 := Subtype.ext this
  rw [← map_natCast (residue 𝒪[K]), h0, map_zero]

end FixedField

end GroundTheory.ProfCoh

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel IsLocalRing IntermediateField

section DegreeZero

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cohomologyConj_zero_eq_id_of_apply (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G)
    [N.Normal] (g : G) (hg : ∀ a : A, A.ρ g a = a) : cohomologyConj A N 0 g = 𝟙 _ := by
  have hinj : Function.Injective (H0Iso (Rep.res N.subtype A)).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine ModuleCat.hom_ext (LinearMap.ext fun x => hinj ?_)
  rw [H0Iso_hom_cohomologyConj]
  exact Subtype.ext (hg _)

end DegreeZero

section Conj

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [ValuativeExtension K Ksep]
  {l : ℕ} {W V : OpenSubgroup Gal(Ksep/K)}

theorem apply_eq_of_valuation_sub_lt_one (hl : (l : 𝓀[K]) ≠ 0)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    {g : Gal(Ksep/K)}
    (hg : ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)), valuation Ksep x ≤ 1 →
      valuation Ksep (g x - x) < 1)
    {ζ : Ksep} (hζ : ζ ^ l = 1) : g ζ = ζ := by
  let := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
  have := isNonarchimedeanLocalField_fixedField V
  have hlF := natCast_residueField_fixedField_ne_zero hl V
  have hl0 : l ≠ 0 := by rintro rfl; simp at hlF
  have hgζ : (g ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  let a : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨ζ, hμ ζ hζ⟩
  let b : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨g ζ, hμ _ hgζ⟩
  have ha : a ^ l = 1 := Subtype.ext (by simpa [a] using hζ)
  have hb : b ^ l = 1 := Subtype.ext (by simpa [b] using hgζ)
  let x : 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] := ⟨a, mem_integer_of_pow_eq_one hl0 ha⟩
  let y : 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] := ⟨b, mem_integer_of_pow_eq_one hl0 hb⟩
  have hx : x ^ l = 1 := Subtype.ext (by simpa [x] using ha)
  have hy : y ^ l = 1 := Subtype.ext (by simpa [y] using hb)
  have hres : residue 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] y =
      residue 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] x := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h1 := valuation_unit hu.unit
    rw [IsUnit.unit_spec] at h1
    have hle : valuation Ksep ζ ≤ 1 :=
      (valuation_le_one_iff_coe _ a).1 ((Valuation.mem_integer_iff _ _).1 x.2)
    have hlt : valuation (fixedField (V : Subgroup Gal(Ksep/K))) (((y - x :
        𝒪[fixedField (V : Subgroup Gal(Ksep/K))])) : fixedField (V : Subgroup Gal(Ksep/K))) < 1 := by
      rw [valuation_lt_one_iff_coe]
      exact hg ζ (hμ ζ hζ) hle
    exact lt_irrefl _ (h1 ▸ hlt)
  have := eq_of_pow_eq_one_of_residue_eq hlF hy hx hres
  exact congrArg (fun z : 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] =>
    ((z : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep)) this

variable (h : V ≤ W) [((V : Subgroup Gal(Ksep/K)).subgroupOf (W : Subgroup Gal(Ksep/K))).Normal]

include h in

theorem cohomologyConj_one_galRootsOfUnity_eq_id (hl : (l : 𝓀[K]) ≠ 0)
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l) (g : (W : Subgroup Gal(Ksep/K)))
    (hg : ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)), valuation Ksep x ≤ 1 →
      valuation Ksep ((g : Gal(Ksep/K)) x - x) < 1) :
    cohomologyConj (Rep.res (W : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf W) 1 g = 𝟙 _ := by
  have hlK := natCast_ne_zero_of_residueField hl
  let := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
  have := isNonarchimedeanLocalField_fixedField V
  have hlF := natCast_residueField_fixedField_ne_zero hl V
  set σ : fixedField (V : Subgroup Gal(Ksep/K)) ≃+* fixedField (V : Subgroup Gal(Ksep/K)) :=
    (fixedFieldConjHom h g).toRingEquiv with hσ
  have hσx : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      ((σ x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = (g : Gal(Ksep/K)) (x : Ksep) :=
    fun x => rfl
  have hval : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      valuation (fixedField (V : Subgroup Gal(Ksep/K))) (σ x) =
        valuation (fixedField (V : Subgroup Gal(Ksep/K))) x := fun x => by
    rw [valuation_eq_iff_coe, hσx]
    exact valuation_algEquiv_apply_of_isAlgebraic (K := K) (g : Gal(Ksep/K)) (x : Ksep)
  have hin : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      valuation (fixedField (V : Subgroup Gal(Ksep/K))) x ≤ 1 →
        valuation (fixedField (V : Subgroup Gal(Ksep/K))) (σ x - x) < 1 := fun x hx => by
    rw [valuation_lt_one_iff_coe]
    rw [valuation_le_one_iff_coe] at hx
    have e : (((σ x - x : fixedField (V : Subgroup Gal(Ksep/K)))) : Ksep) =
        (g : Gal(Ksep/K)) (x : Ksep) - x := by
      rw [← hσx]
      rfl
    rw [e]
    exact hg x x.2 hx
  have hiter : ∀ (j : ℕ) (x : fixedField (V : Subgroup Gal(Ksep/K))),
      ((σ^[j] x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = ((g : Gal(Ksep/K)) ^ j) (x : Ksep) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', hσx, ih, pow_succ', AlgEquiv.mul_apply]
  have hσm : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      σ^[(V : Subgroup Gal(Ksep/K)).relIndex W] x = x := fun x => by
    apply Subtype.ext
    rw [hiter]
    have hmem := Subgroup.pow_index_mem ((V : Subgroup Gal(Ksep/K)).subgroupOf W) g
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hmem
    exact (mem_fixedField_iff _ _).1 x.2 _ hmem
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨u, rfl⟩ := kummerOpenHom_surjective h hlK x
  change (cohomologyConj _ _ 1 g).hom (kummerOpenHom h hlK u) = kummerOpenHom h hlK u
  rw [← kummerOpenHom_smul, ← sub_eq_zero, ← map_sub, kummerOpenHom_eq_zero_iff]
  obtain ⟨y, hy⟩ := exists_map_units_eq_mul_pow hlF σ hval hin hind hσm (Additive.toMul u)
  refine ⟨Additive.ofMul y, ?_⟩
  have hsm : Additive.toMul (fixedFieldConjHom h g • u) =
      Units.map (σ : fixedField (V : Subgroup Gal(Ksep/K)) →* fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive.toMul u) :=
    Units.ext (Subtype.ext rfl)
  rw [eq_sub_iff_add_eq, add_comm]
  apply Additive.toMul.injective
  rw [toMul_add, toMul_nsmul, toMul_ofMul, hsm, hy]

include h in

theorem cohomologyConj_galRootsOfUnity_eq_id (hl : (l : 𝓀[K]) ≠ 0)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l) (g : (W : Subgroup Gal(Ksep/K)))
    (hg : ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)), valuation Ksep x ≤ 1 →
      valuation Ksep ((g : Gal(Ksep/K)) x - x) < 1) {n : ℕ} (hn : n ≤ 2) :
    cohomologyConj (Rep.res (W : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf W) n g = 𝟙 _ := by
  interval_cases n
  · refine cohomologyConj_zero_eq_id_of_apply _ _ g fun a => ?_
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    exact apply_eq_of_valuation_sub_lt_one hl hμ hg
      (by
        have h1 := congrArg Units.val ((mem_rootsOfUnity l _).1 (Additive.toMul a).2)
        rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
        convert h1 using 2
        rfl)
  · exact cohomologyConj_one_galRootsOfUnity_eq_id h hl hind g hg
  · exact cohomologyConj_two_galRootsOfUnity_eq_id (natCast_ne_zero_of_residueField hl) h g

end Conj

end GroundTheory.ProfCoh

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel IsLocalRing IntermediateField

section Helpers

def addHomToULiftLinear {M N : Type*} [AddCommGroup M] [AddCommGroup N] {iM : Module (ULift.{0} ℤ) M}
    {iN : Module (ULift.{0} ℤ) N} (f : M →+ N) :
    @LinearMap (ULift.{0} ℤ) (ULift.{0} ℤ) _ _ (RingHom.id _) M N _ _ iM iN where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨n⟩ := c
    have h1 := @Int.cast_smul_eq_zsmul (ULift.{0} ℤ) M _ _ iM n x
    have h2 := @Int.cast_smul_eq_zsmul (ULift.{0} ℤ) N _ _ iN n (f x)
    have e : ((n : ℤ) : ULift.{0} ℤ) = ULift.up n := rfl
    rw [RingHom.id_apply, ← e, h1, h2, map_zsmul]

theorem addHomToULiftLinear_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {iM : Module (ULift.{0} ℤ) M} {iN : Module (ULift.{0} ℤ) N} (f : M →+ N) (x : M) :
    (addHomToULiftLinear (iM := iM) (iN := iN) f) x = f x :=
  rfl

theorem exists_sum_addHom_comp_eq {l : ℕ} [Fact l.Prime] {T A : Type*} [AddCommGroup T]
    [AddCommGroup A] [Module (ZMod l) A] [Finite A] (e : ZMod l ≃+ T) :
    ∃ (ι : Type) (_ : Fintype ι) (i : ι → (T →+ A)) (p : ι → (A →+ T)),
      ∀ a : A, ∑ j, i j (p j a) = a := by
  obtain ⟨n, b⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (ZMod l) A) := by
    have : Module.Finite (ZMod l) A := Module.Finite.of_finite
    exact ⟨_, ⟨Module.finBasis (ZMod l) A⟩⟩
  obtain ⟨b⟩ := b
  refine ⟨Fin n, inferInstance, fun j => (LinearMap.toSpanSingleton (ZMod l) A (b j)).toAddMonoidHom.comp
    e.symm.toAddMonoidHom, fun j => e.toAddMonoidHom.comp (b.coord j).toAddMonoidHom, fun a => ?_⟩
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply]
  exact b.sum_repr a

end Helpers

section LemmaY

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [ValuativeExtension K Ksep]
  {l : ℕ}

theorem subsingleton_cohomology_of_inertia_open (hlp : l.Prime) (hl : (l : 𝓀[K]) ≠ 0)
    {W V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ W)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (W : Subgroup Gal(Ksep/K))).Normal]
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (hin : ∀ g : (W : Subgroup Gal(Ksep/K)), ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)),
      valuation Ksep x ≤ 1 → valuation Ksep ((g : Gal(Ksep/K)) x - x) < 1)
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l)
    (A : Rep (ULift.{0} ℤ) (W : Subgroup Gal(Ksep/K))) [IsDiscreteRep A] [Finite A]
    (hA : ∀ a : A, l • a = 0)
    (hV : ∀ g : (W : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ (V : Subgroup Gal(Ksep/K)) →
      ∀ a : A, A.ρ g a = a)
    (hinv : ∀ a : A, (∀ g : (W : Subgroup Gal(Ksep/K)), A.ρ g a = a) → a = 0)
    {n : ℕ} (hn : n ≤ 2) : Subsingleton (cohomology A n) := by
  have hlK := natCast_ne_zero_of_residueField hl
  have : Fact l.Prime := ⟨hlp⟩
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ksep hlp hlK
  let : Module (ZMod l) A := AddCommGroup.zmodModule hA
  let T := Rep.res (W : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)
  obtain ⟨ι, _, i, p, hip⟩ := exists_sum_addHom_comp_eq (T := T) (A := A) e
  have hT : ∀ (g : (W : Subgroup Gal(Ksep/K))) (t : T), T.ρ g t = t := fun g t => by
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    exact apply_eq_of_valuation_sub_lt_one hl hμ (hin g) (by
      have h1 := congrArg Units.val ((mem_rootsOfUnity l _).1 (Additive.toMul t).2)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
      convert h1 using 2
      rfl)
  have hbij : Function.Bijective fun a : A =>
      ((openSubgroupOf W V : OpenSubgroup (W : Subgroup Gal(Ksep/K))) :
        Subgroup (W : Subgroup Gal(Ksep/K))).index • a := by
    set m := ((openSubgroupOf W V : OpenSubgroup (W : Subgroup Gal(Ksep/K))) :
        Subgroup (W : Subgroup Gal(Ksep/K))).index
    have hm : m.Coprime l := hind
    set u := ZMod.unitOfCoprime m hm
    have hu : ∀ a : A, m • a = (u : ZMod l) • a := fun a => by
      rw [ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul]
    refine Function.bijective_iff_has_inverse.2 ⟨fun a => ((u⁻¹ : (ZMod l)ˣ) : ZMod l) • a,
      fun a => ?_, fun a => ?_⟩
    · simp only [hu, smul_smul, Units.inv_mul, one_smul]
    · simp only [hu, smul_smul, Units.mul_inv, one_smul]
  exact subsingleton_cohomology_of_sum (openSubgroupOf W V) hT
    (fun m a => hV m ((Subgroup.mem_subgroupOf).1 m.2) a) hinv hbij
    (fun j => addHomToULiftLinear (i j)) (fun j => addHomToULiftLinear (p j))
    (DFunLike.ext _ _ fun a => by simpa [LinearMap.sum_apply, addHomToULiftLinear_apply] using hip a) n
    (fun g => cohomologyConj_galRootsOfUnity_eq_id h hl hμ hind g (hin g) hn)

theorem subsingleton_cohomology_of_inertia (hlp : l.Prime) (hl : (l : 𝓀[K]) ≠ 0)
    {W V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ W) [(W : Subgroup Gal(Ksep/K)).Normal]
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (W : Subgroup Gal(Ksep/K))).Normal]
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (hin : ∀ g ∈ (W : Subgroup Gal(Ksep/K)), ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)),
      valuation Ksep x ≤ 1 → valuation Ksep (g x - x) < 1)
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l)
    (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, l • m = 0)
    (hV : ∀ g ∈ (V : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m)
    (hW : ∀ m : M, (∀ g ∈ (W : Subgroup Gal(Ksep/K)), M.ρ g m = m) → m = 0)
    {i : ℕ} (hi : i ≤ 2) : Subsingleton (cohomology M i) := by
  refine subsingleton_cohomology_of_normal (W : Subgroup Gal(Ksep/K)) W.isClosed M
    (fun m hm => hW m fun g hg => hm ⟨g, hg⟩) 2 (fun j _ hj => ?_) i hi
  have : Finite (Rep.res (W : Subgroup Gal(Ksep/K)).subtype M) := ‹Finite M›
  exact subsingleton_cohomology_of_inertia_open hlp hl h hμ (fun g => hin g g.2) hind
    (Rep.res (W : Subgroup Gal(Ksep/K)).subtype M) hM (fun g hg m => hV g hg m)
    (fun m hm => hW m fun g hg => hm ⟨g, hg⟩) hj

end LemmaY

end GroundTheory.ProfCoh

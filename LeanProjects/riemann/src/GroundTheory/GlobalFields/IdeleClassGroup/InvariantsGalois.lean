import Mathlib
import GroundTheory.GlobalFields.IdeleClassGroup.Invariants
import GroundTheory.LocalFields.CompleteTrivial

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

theorem ofOpenSubgroup_le {U U' : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} (h : U' ≤ U) :
    ofOpenSubgroup U ≤ ofOpenSubgroup U' :=
  show fixedField (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ≤ fixedField (U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) from
    fun x hx ↦ (mem_fixedField_iff _ x).2 fun g hg ↦ (mem_fixedField_iff _ x).1 hx g (h hg)

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield

theorem coe_norm_of_eq {K L : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} [(L.subgroupOf K).FiniteIndex]
    {F E : FiniteSubfield} (h : F ≤ E) (hK : K = F.1.fixingSubgroup) (hL : L = E.1.fixingSubgroup)
    (c : IdeleClassGroup E.1) (hc : of E c ∈ fixedModule IdeleClassLimit L) :
    (norm IdeleClassLimit K L ⟨of E c, hc⟩ : IdeleClassLimit) =
      of F (FiniteSubfield.ideleClassNorm h c) := by
  subst hK hL
  exact congrArg Subtype.val (norm_fixedEquiv h c)

theorem coe_norm_openSubgroup {U U' : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} (hUU' : U' ≤ U)
    (c : IdeleClassGroup (ofOpenSubgroup U').1)
    (hc : of (ofOpenSubgroup U') c ∈ fixedModule IdeleClassLimit (U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) :
    (norm IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
      ⟨of (ofOpenSubgroup U') c, hc⟩ : IdeleClassLimit) =
      of (ofOpenSubgroup U) (FiniteSubfield.ideleClassNorm (ofOpenSubgroup_le hUU') c) :=
  coe_norm_of_eq (ofOpenSubgroup_le hUU') (fixingSubgroup_ofOpenSubgroup U).symm
    (fixingSubgroup_ofOpenSubgroup U').symm c hc

end IdeleClassLimit

namespace FiniteSubfield

instance algebraOfFact {F E : FiniteSubfield} [h : Fact (F ≤ E)] : Algebra F.1 E.1 :=
  algebraOfLE h.out

instance {F E : FiniteSubfield} [Fact (F ≤ E)] : IsScalarTower ℚ F.1 E.1 :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

instance {F E : FiniteSubfield} [Fact (F ≤ E)] : FiniteDimensional F.1 E.1 :=
  FiniteDimensional.right ℚ F.1 E.1

theorem apply_mem_of_normal {F E : FiniteSubfield} (h : F ≤ E)
    [hN : (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal] {g : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hg : g ∈ F.1.fixingSubgroup) {x : ℚ̄} (hx : x ∈ E.1) : g x ∈ E.1 := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E.1, mem_fixedField_iff]
  intro l hl
  have hc : g⁻¹ * l * g ∈ E.1.fixingSubgroup := by
    have h1 := hN.conj_mem ⟨l, IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h) hl⟩
      (by rwa [Subgroup.mem_subgroupOf]) (⟨g, hg⟩ : F.1.fixingSubgroup)⁻¹
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hc x hx
  calc l (g x) = g ((g⁻¹ * l * g) x) := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g, mul_inv_cancel,
          AlgEquiv.one_apply]
    _ = g x := by rw [h2]

variable {F E : FiniteSubfield} [hFE : Fact (F ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]

def restrictHom : F.1.fixingSubgroup →* (E.1 ≃ₐ[F.1] E.1) where
  toFun g := AlgEquiv.ofRingEquiv (f :=
      { toFun := fun x ↦ ⟨(g : ℚ̄ ≃ₐ[ℚ] ℚ̄) x, apply_mem_of_normal hFE.out g.2 x.2⟩
        invFun := fun x ↦ ⟨(g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ x, apply_mem_of_normal hFE.out (inv_mem g.2) x.2⟩
        left_inv := fun x ↦ Subtype.ext (by
          change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) x) = x
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
        right_inv := fun x ↦ Subtype.ext (by
          change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ x) = x
          rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
        map_mul' := fun x y ↦ Subtype.ext (map_mul (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄) y)
        map_add' := fun x y ↦ Subtype.ext (map_add (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄) y) })
      (fun x ↦ Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff F.1 _).1 g.2 x x.2))
  map_one' := AlgEquiv.ext fun _ ↦ Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ Subtype.ext rfl

@[simp]
theorem coe_restrictHom_apply (g : F.1.fixingSubgroup) (x : E.1) :
    ((restrictHom g x : E.1) : ℚ̄) = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) x :=
  rfl

theorem restrictHom_surjective :
    Function.Surjective (restrictHom : F.1.fixingSubgroup →* (E.1 ≃ₐ[F.1] E.1)) := by
  intro σ
  let σ' : ℚ̄ ≃ₐ[ℚ] ℚ̄ := (σ.restrictScalars ℚ).liftNormal ℚ̄
  have hσ' : ∀ x : E.1, σ' x = σ x := fun x ↦ (σ.restrictScalars ℚ).liftNormal_commutes ℚ̄ x
  have hmem : σ' ∈ F.1.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 := hσ' (algebraMap F.1 E.1 ⟨x, hx⟩)
    rw [σ.commutes] at h1
    exact h1
  exact ⟨⟨σ', hmem⟩, AlgEquiv.ext fun x ↦ Subtype.ext (hσ' x)⟩

theorem ker_restrictHom :
    (restrictHom : F.1.fixingSubgroup →* (E.1 ≃ₐ[F.1] E.1)).ker =
      E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    exact congrArg (fun σ : E.1 ≃ₐ[F.1] E.1 ↦ ((σ ⟨x, hx⟩ : E.1) : ℚ̄)) hg
  · intro hg
    exact AlgEquiv.ext fun x ↦ Subtype.ext (hg x x.2)

theorem isGalois_of_normal : IsGalois F.1 E.1 := by
  apply IsGalois.of_card_aut_eq_finrank
  have h1 : E.1.fixingSubgroup.relIndex F.1.fixingSubgroup = Module.finrank F.1 E.1 :=
    relIndex_fixingSubgroup hFE.out
  rw [← h1, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (restrictHom_surjective (F := F) (E := E))).toEquiv, ker_restrictHom]
  rfl

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield GroundTheory.LocalField

variable {F E : FiniteSubfield} [hFE : Fact (F ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]

theorem smul_of_of_normal (g : F.1.fixingSubgroup) (c : IdeleClassGroup E.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • of E c = of E (restrictHom (E := E) g • c) :=
  smul_of_eq_of_ideleClassEquiv _ ((restrictHom (E := E) g : E.1 ≃ₐ[F.1] E.1) : E.1 ≃+* E.1)
    (fun _ ↦ rfl) c

theorem mem_invariants_iff (c : IdeleClassGroup E.1) :
    c ∈ invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) ↔
      of E c ∈ fixedModule IdeleClassLimit F.1.fixingSubgroup := by
  constructor
  · intro hc g hg
    exact (smul_of_of_normal ⟨g, hg⟩ c).trans (congrArg _ (hc _))
  · intro hc σ
    obtain ⟨g, rfl⟩ := restrictHom_surjective σ
    apply of_injective E
    rw [← smul_of_of_normal g]
    exact hc g g.2

def invariantsEquiv :
    invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) ≃*
      fixedModule IdeleClassLimit F.1.fixingSubgroup :=
  (MonoidHom.ofInjective (f := (of E).comp (invariants (E.1 ≃ₐ[F.1] E.1) _).subtype)
    ((of_injective E).comp Subtype.val_injective)).trans (MulEquiv.subgroupCongr (by
      ext a
      constructor
      · rintro ⟨c, rfl⟩
        exact (mem_invariants_iff (c : IdeleClassGroup E.1)).1 c.2
      · intro ha
        have ha' := fixedModule_anti (IntermediateField.fixingSubgroup_le
          (show F.1 ≤ E.1 from hFE.out)) ha
        rw [fixedModule_fixingSubgroup] at ha'
        obtain ⟨c, rfl⟩ := ha'
        exact ⟨⟨c, (mem_invariants_iff c).2 ha⟩, rfl⟩))

@[simp]
theorem coe_invariantsEquiv (c : invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)) :
    (invariantsEquiv c : IdeleClassLimit) = of E c :=
  rfl

theorem of_tateNorm (c : IdeleClassGroup E.1) :
    of E (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) c) =
      of F (FiniteSubfield.ideleClassNorm hFE.out c) := by
  have := isGalois_of_normal (F := F) (E := E)
  rw [tateNorm_apply, ← ideleClassMap_ideleClassNorm]
  exact of_ideleClassMap hFE.out _

theorem tateNorm_eq_one_iff (c : IdeleClassGroup E.1) :
    tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) c = 1 ↔
      norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup (fixedEquiv E c) = 1 := by
  constructor
  · intro h1
    apply Subtype.ext
    rw [norm_fixedEquiv hFE.out, coe_fixedEquiv, ← of_tateNorm, h1, map_one]
    rfl
  · intro h1
    apply of_injective E
    rw [of_tateNorm, map_one, ← coe_fixedEquiv, ← norm_fixedEquiv hFE.out, h1]
    rfl

theorem map_augmentation :
    (GroundTheory.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).map (of E) =
      Abstract.augmentation IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup := by
  rw [GroundTheory.LocalField.augmentation, MonoidHom.map_closure, Abstract.augmentation]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨σ, c, rfl⟩, rfl⟩
    obtain ⟨g, rfl⟩ := restrictHom_surjective σ
    refine ⟨g, g.2, of E c, ?_, ?_⟩
    · rw [fixedModule_fixingSubgroup]
      exact ⟨c, rfl⟩
    · rw [map_div, smul_of_of_normal g c]
  · rintro ⟨g, hg, a, ha, rfl⟩
    rw [fixedModule_fixingSubgroup] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨restrictHom ⟨g, hg⟩ • c / c, ⟨_, c, rfl⟩, by
      rw [map_div, ← smul_of_of_normal ⟨g, hg⟩ c]⟩

theorem coe_invariantsEquiv_tateNorm (c : IdeleClassGroup E.1) :
    (invariantsEquiv ⟨tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) c,
      tateNorm_mem_invariants c⟩ : IdeleClassLimit) =
      norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup (fixedEquiv E c) := by
  rw [coe_invariantsEquiv, norm_fixedEquiv hFE.out, coe_fixedEquiv]
  exact of_tateNorm c

theorem map_range_tateNorm :
    ((tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).range.subgroupOf
      (invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1))).map
        (invariantsEquiv (F := F) (E := E) : invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) →*
          fixedModule IdeleClassLimit F.1.fixingSubgroup) =
      (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).range := by
  apply le_antisymm
  · rintro _ ⟨⟨y, hy⟩, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨fixedEquiv E c, Subtype.ext (coe_invariantsEquiv_tateNorm c).symm⟩
  · rintro _ ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (fixedEquiv E).surjective b
    exact ⟨⟨tateNorm _ _ c, tateNorm_mem_invariants c⟩, ⟨c, rfl⟩,
      Subtype.ext (coe_invariantsEquiv_tateNorm c)⟩

def tateZeroEquivGalois :
    tateZero IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup ≃*
      TateZero (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) :=
  haveI : ((tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).range.subgroupOf
      (invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1))).Normal :=
    ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  (QuotientGroup.congr ((tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).range.subgroupOf
      (invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)))
    (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).range invariantsEquiv
    map_range_tateNorm).symm

def kerEquiv :
    (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker ≃*
      (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker :=
  ((fixedEquiv E).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact (tateNorm_eq_one_iff c).1 hc
    · intro a ha
      obtain ⟨c, rfl⟩ := (fixedEquiv E).surjective a
      exact ⟨c, (tateNorm_eq_one_iff c).2 ha, rfl⟩))

@[simp]
theorem coe_coe_kerEquiv (c : (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker) :
    ((kerEquiv c : fixedModule IdeleClassLimit E.1.fixingSubgroup) : IdeleClassLimit) = of E c :=
  rfl

theorem map_augmentation_subgroupOf :
    ((GroundTheory.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).subgroupOf
      (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker).map
        (kerEquiv (F := F) (E := E) : (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker →*
          (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker) =
      (Abstract.augmentation IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).comap
        ((fixedModule IdeleClassLimit E.1.fixingSubgroup).subtype.comp
          (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker.subtype) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap]
    change of E (x : IdeleClassGroup E.1) ∈ _
    rw [← map_augmentation]
    exact Subgroup.mem_map_of_mem _ hx
  · intro y hy
    obtain ⟨x, rfl⟩ := kerEquiv.surjective y
    rw [Subgroup.mem_comap] at hy
    change of E (x : IdeleClassGroup E.1) ∈ _ at hy
    rw [← map_augmentation, Subgroup.mem_map_iff_mem (of_injective E)] at hy
    exact ⟨x, Subgroup.mem_subgroupOf.2 hy, rfl⟩

def tateNegOneEquivGalois :
    tateNegOne IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup ≃*
      TateNegOne (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) :=
  haveI : ((GroundTheory.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).subgroupOf
      (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker).Normal :=
    ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  (QuotientGroup.congr ((GroundTheory.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1)
      (IdeleClassGroup E.1)).subgroupOf (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker)
    ((Abstract.augmentation IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).comap
      ((fixedModule IdeleClassLimit E.1.fixingSubgroup).subtype.comp
        (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker.subtype))
    kerEquiv map_augmentation_subgroupOf).symm

end IdeleClassLimit

end

end GroundTheory.Global

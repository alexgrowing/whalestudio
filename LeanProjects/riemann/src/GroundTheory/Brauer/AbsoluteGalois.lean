import Mathlib
import GroundTheory.Brauer.CrossedProductIso
import GroundTheory.Brauer.Inflation
import GroundTheory.Brauer.Splitting
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

namespace H2mul

section Bridge

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem ofMul_mem_cocycles₂_galUnits (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    (fun p => Additive.ofMul ((c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) p)) ∈
      cocycles₂ (galUnits.{u} K L) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  exact congrArg Additive.ofMul ((mem_mulCocycles₂_iff _).1 c.2 g h j)

def galUnitsCocycle (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) : cocycles₂ (galUnits.{u} K L) :=
  ⟨_, ofMul_mem_cocycles₂_galUnits c⟩

@[simp]
theorem galUnitsCocycle_apply (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) :
    galUnitsCocycle c p = Additive.ofMul ((c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) p) :=
  rfl

def toGalUnitsH2 : mulCocycles₂ (L ≃ₐ[K] L) Lˣ →* Multiplicative (H2 (galUnits.{u} K L)) where
  toFun c := Multiplicative.ofAdd (H2π (galUnits.{u} K L) (galUnitsCocycle c))
  map_one' := by
    have h0 : galUnitsCocycle (1 : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) = 0 := Subtype.ext rfl
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    rw [h0, map_zero]
  map_mul' c c' := by
    rw [← ofAdd_add]
    congr 1
    rw [← map_add]
    rfl

theorem toGalUnitsH2_eq_one_iff (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    toGalUnitsH2 c = 1 ↔ IsMulCoboundary₂ (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) := by
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, H2π_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun g => Additive.toMul (x g), fun g h => ?_⟩
    exact congrArg Additive.toMul (congrFun hx (g, h))
  · rintro ⟨x, hx⟩
    exact ⟨fun g => Additive.ofMul (x g), funext fun p => congrArg Additive.ofMul (hx p.1 p.2)⟩

def galUnitsEquivH2 : H2mul (L ≃ₐ[K] L) Lˣ ≃* Multiplicative (H2 (galUnits.{u} K L)) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ toGalUnitsH2 (fun c hc => (toGalUnitsH2_eq_one_iff c).2 hc)) (by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x
      induction x using induction_on with
      | h c =>
        intro hx
        exact (mk_eq_one_iff c).2 ((toGalUnitsH2_eq_one_iff c).1 hx)
    · intro y
      induction y using Multiplicative.rec with
      | ofAdd y =>
      induction y using H2_induction_on with
      | h y =>
      refine ⟨mk _ _ ⟨fun p => Additive.toMul (y p), fun g h j => ?_⟩, rfl⟩
      exact congrArg Additive.toMul ((mem_cocycles₂_iff (y : _ → Additive Lˣ)).1 y.2 g h j))

@[simp]
theorem galUnitsEquivH2_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    galUnitsEquivH2 (mk _ _ c) = Multiplicative.ofAdd (H2π (galUnits.{u} K L) (galUnitsCocycle c)) :=
  rfl

end Bridge

end H2mul

section Tower

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
  [Algebra E F] [IsScalarTower K E F] [Normal K E]

variable (K E F) in

def galUnitsInclusion :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K F :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Fˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E F : E →+* F) : E →* F))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩

@[simp]
theorem galUnitsInclusion_hom_apply (x : Additive Eˣ) :
    ((Additive.toMul (α := Fˣ) ((galUnitsInclusion K E F).hom x) : Fˣ) : F) =
      algebraMap E F ((Additive.toMul (α := Eˣ) x : Eˣ) : E) :=
  rfl

theorem galUnitsEquivH2_inflation (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    H2mul.galUnitsEquivH2 (H2mul.inflation K E F x) = Multiplicative.ofAdd
      (groupCohomology.map (AlgEquiv.restrictNormalHom E) (galUnitsInclusion K E F) 2
        (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x))) := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [H2mul.inflation_mk, H2mul.galUnitsEquivH2_mk, H2mul.galUnitsEquivH2_mk, toAdd_ofAdd,
    H2π_comp_map_apply]
  congr 2

end Tower

section Absolute

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

theorem coe_algebraMap_intermediateField {E F : IntermediateField K Ks} [Algebra E F]
    [IsScalarTower E F Ks] (y : E) : ((algebraMap E F y : F) : Ks) = (y : Ks) :=
  (IsScalarTower.algebraMap_apply E F Ks y).symm

variable [IsGalois K Ks]

variable (K) in

def unitsInflationH2 (E : IntermediateField K Ks) [FiniteDimensional K E] [Normal K E] :
    H2 (galUnits.{u} K E) ⟶ cohomology (galUnits.{u} K Ks) 2 :=
  HomologicalComplex.homologyMap (unitsInflationCochains E) 2

theorem map_comp_unitsInflationH2 (E F : IntermediateField K Ks) [FiniteDimensional K E]
    [Normal K E] [FiniteDimensional K F] [Normal K F] [Algebra E F] [IsScalarTower K E F]
    [IsScalarTower E F Ks] :
    groupCohomology.map (AlgEquiv.restrictNormalHom E) (galUnitsInclusion K E F) 2 ≫
      unitsInflationH2 K F = unitsInflationH2 K E := by
  unfold unitsInflationH2
  refine (HomologicalComplex.homologyMap_comp _ _ 2).symm.trans ?_
  congr 1
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K Ks)).f n), HomologicalComplex.comp_f,
    Category.assoc]
  have hE := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (unitsInflationCochains_comp_cochainsComplexι (L := Ks) E)
  have hF := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (unitsInflationCochains_comp_cochainsComplexι (L := Ks) F)
  simp only [HomologicalComplex.comp_f] at hE hF
  rw [hE, hF, ← HomologicalComplex.comp_f, ← groupCohomology.cochainsMap_comp]
  congr 1
  refine cochainsMap_congr ?_ ?_
  · exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp K E F Ks).symm
  · refine LinearMap.ext fun x => Additive.toMul.injective (Units.ext ?_)
    exact coe_algebraMap_intermediateField ((Additive.toMul (α := Eˣ) x : Eˣ) : E)

theorem inflation_eq_iso_comp_unitsInflationH2 (U : OpenNormalSubgroup (Ks ≃ₐ[K] Ks)) :
    inflation (galUnits.{u} K Ks) U 2 = (groupCohomologyQuotientGalUnitsIso U 2).hom ≫
      unitsInflationH2 K (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks))) := by
  rw [groupCohomologyQuotientGalUnitsIso, mapIso_hom]
  unfold unitsInflationH2 inflation
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ 2)
  congr 1
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι (galUnits.{u} K Ks)).f n), HomologicalComplex.comp_f,
    Category.assoc]
  have hU := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (inflationCochains_comp_cochainsComplexι (galUnits.{u} K Ks) U)
  have hE := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (unitsInflationCochains_comp_cochainsComplexι (L := Ks)
      (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks))))
  simp only [HomologicalComplex.comp_f] at hU hE
  rw [hU, hE, ← HomologicalComplex.comp_f, ← groupCohomology.cochainsMap_comp]
  congr 1
  refine cochainsMap_congr ?_ ?_
  · refine MonoidHom.ext fun σ => ?_
    change (σ : _ ⧸ _) = (quotientEquivGal U).symm (AlgEquiv.restrictNormalHom _ σ)
    rw [eq_comm, MulEquiv.symm_apply_eq]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [quotientEquivGal_mk_apply, AlgEquiv.restrictNormalHom_apply]
  · exact LinearMap.ext fun x => Additive.toMul.injective (Units.ext rfl)

theorem transition_comp_iso_hom {U V : OpenNormalSubgroup (Ks ≃ₐ[K] Ks)} (h : V ≤ U)
    [Algebra (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
      (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))]
    [IsScalarTower K (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
      (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))]
    [IsScalarTower (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
      (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks))) Ks] :
    transition (galUnits.{u} K Ks) h 2 ≫ (groupCohomologyQuotientGalUnitsIso V 2).hom =
      (groupCohomologyQuotientGalUnitsIso U 2).hom ≫
        groupCohomology.map (AlgEquiv.restrictNormalHom _)
          (galUnitsInclusion K (IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))
            (IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))) 2 := by
  rw [groupCohomologyQuotientGalUnitsIso, groupCohomologyQuotientGalUnitsIso, mapIso_hom,
    mapIso_hom, transition, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ 2
  · refine MonoidHom.ext fun τ => ?_
    obtain ⟨q, rfl⟩ := (quotientEquivGal V).surjective τ
    induction q using QuotientGroup.induction_on with
    | H σ =>
    change quotientMapOfLE h ((quotientEquivGal V).symm (quotientEquivGal V σ)) =
      (quotientEquivGal U).symm (AlgEquiv.restrictNormalHom _ (quotientEquivGal V σ))
    rw [MulEquiv.symm_apply_apply, quotientMapOfLE_mk, eq_comm, MulEquiv.symm_apply_eq]
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [quotientEquivGal_mk_apply, ← coe_algebraMap_intermediateField
      (F := IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks))),
      CrossedProduct.algebraMap_restrictNormalHom, quotientEquivGal_mk_apply,
      coe_algebraMap_intermediateField]
  · refine LinearMap.ext fun x => Additive.toMul.injective (Units.ext ?_)
    exact Subtype.ext (coe_algebraMap_intermediateField
      (F := IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks)))
      (⟨_, mem_fixedField_of_mem_invariants_galUnits _ x.2⟩ :
        IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)))).symm

end Absolute

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

section Galois

variable [IsGalois K Ks]

variable (K) in

def inflationToAbsolute (E : IntermediateField K Ks) [FiniteDimensional K E] [IsGalois K E] :
    H2mul (E ≃ₐ[K] E) Eˣ →* Multiplicative (cohomology (galUnits.{u} K Ks) 2) :=
  (AddMonoidHom.toMultiplicative (unitsInflationH2 K E).hom.toAddMonoidHom).comp
    (H2mul.galUnitsEquivH2 : H2mul (E ≃ₐ[K] E) Eˣ ≃* _).toMonoidHom

theorem inflationToAbsolute_apply (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    inflationToAbsolute K E x = Multiplicative.ofAdd
      ((unitsInflationH2 K E).hom (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x))) :=
  rfl

theorem inflationToAbsolute_inflation (E F : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] [FiniteDimensional K F] [IsGalois K F] [Algebra E F] [IsScalarTower K E F]
    [IsScalarTower E F Ks] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    inflationToAbsolute K F (H2mul.inflation K E F x) = inflationToAbsolute K E x := by
  rw [inflationToAbsolute_apply, inflationToAbsolute_apply, galUnitsEquivH2_inflation, toAdd_ofAdd]
  congr 1
  exact congrArg (fun φ => φ.hom (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x)))
    (map_comp_unitsInflationH2 E F)

theorem exists_inflationToAbsolute_eq (x : Multiplicative (cohomology (galUnits.{u} K Ks) 2)) :
    ∃ (E : IntermediateField K Ks) (_ : FiniteDimensional K E) (_ : IsGalois K E)
      (y : H2mul (E ≃ₐ[K] E) Eˣ), inflationToAbsolute K E y = x := by
  obtain ⟨U, z, hz⟩ := exists_inflation_eq (galUnits.{u} K Ks) 2 (Multiplicative.toAdd x)
  refine ⟨IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks)), inferInstance, inferInstance,
    H2mul.galUnitsEquivH2.symm
      (Multiplicative.ofAdd ((groupCohomologyQuotientGalUnitsIso U 2).hom z)), ?_⟩
  rw [inflationToAbsolute_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, ← hz, inflation_eq_iso_comp_unitsInflationH2]
  rfl

theorem inflationToAbsolute_injective (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] : Function.Injective (inflationToAbsolute K E) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  let U : OpenNormalSubgroup (Ks ≃ₐ[K] Ks) :=
    fixingOpenNormalSubgroup ({ toIntermediateField := E } : FiniteGaloisIntermediateField K Ks)
  let E' := IntermediateField.fixedField (U : Subgroup (Ks ≃ₐ[K] Ks))
  have hEE' : E ≤ E' := fun x hx => (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
  let _ : Algebra E E' := (IntermediateField.inclusion hEE').toAlgebra
  have : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E E' Ks := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← inflationToAbsolute_inflation E E'] at hy
  set y' := H2mul.inflation K E E' y with hy'
  set z := Multiplicative.toAdd (H2mul.galUnitsEquivH2 y') with hz
  obtain ⟨V, hVU, hV⟩ := exists_transition_eq_zero (galUnits.{u} K Ks) 2 U
    ((groupCohomologyQuotientGalUnitsIso U 2).inv z) (by
      rw [inflation_eq_iso_comp_unitsInflationH2]
      change (unitsInflationH2 K E').hom
        ((groupCohomologyQuotientGalUnitsIso U 2).hom.hom
          ((groupCohomologyQuotientGalUnitsIso U 2).inv.hom z)) = 0
      rw [Iso.inv_hom_id_apply]
      exact congrArg Multiplicative.toAdd hy)
  let E'' := IntermediateField.fixedField (V : Subgroup (Ks ≃ₐ[K] Ks))
  have hE'E'' : E' ≤ E'' := fun x hx => (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
    (IntermediateField.mem_fixedField_iff _ _).1 hx σ (hVU hσ)
  let _ : Algebra E' E'' := (IntermediateField.inclusion hE'E'').toAlgebra
  have : IsScalarTower K E' E'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E' E'' Ks := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := congrArg (groupCohomologyQuotientGalUnitsIso V 2).hom.hom hV
  rw [map_zero] at h2
  change (transition (galUnits.{u} K Ks) hVU 2 ≫ (groupCohomologyQuotientGalUnitsIso V 2).hom).hom
    ((groupCohomologyQuotientGalUnitsIso U 2).inv.hom z) = 0 at h2
  rw [transition_comp_iso_hom hVU] at h2
  change (groupCohomology.map (AlgEquiv.restrictNormalHom _) (galUnitsInclusion K E' E'') 2).hom
    ((groupCohomologyQuotientGalUnitsIso U 2).hom.hom
      ((groupCohomologyQuotientGalUnitsIso U 2).inv.hom z)) = 0 at h2
  rw [Iso.inv_hom_id_apply, hz] at h2
  have h3 : H2mul.galUnitsEquivH2 (H2mul.inflation K E' E'' y') = 1 := by
    rw [galUnitsEquivH2_inflation, h2]
    rfl
  rw [MulEquivClass.map_eq_one_iff] at h3
  have h4 : y' = 1 := H2mul.inflation_injective (K := K) (L := E') (L' := E'') (by rw [h3, map_one])
  exact H2mul.inflation_injective (K := K) (L := E) (L' := E') (by rw [← hy', h4, map_one])

theorem inflationToAbsolute_symm_relBrauerEquiv_of_le {E F : IntermediateField K Ks}
    [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K F] [IsGalois K F] (hEF : E ≤ F)
    (b : BrauerGroup.{u, u} K) (hb : b ∈ BrauerGroup.relBrauer K E)
    (hb' : b ∈ BrauerGroup.relBrauer K F) :
    inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) =
      inflationToAbsolute K F ((H2mul.relBrauerEquiv K F).symm ⟨b, hb'⟩) := by
  let _ : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E F Ks := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← inflationToAbsolute_inflation E F]
  congr 1
  apply (H2mul.relBrauerEquiv K F).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [H2mul.coe_relBrauerEquiv, H2mul.toBrauer_inflation, ← H2mul.coe_relBrauerEquiv,
    MulEquiv.apply_symm_apply]

theorem inflationToAbsolute_symm_relBrauerEquiv_eq {E F : IntermediateField K Ks}
    [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K F] [IsGalois K F]
    (b : BrauerGroup.{u, u} K) (hb : b ∈ BrauerGroup.relBrauer K E)
    (hb' : b ∈ BrauerGroup.relBrauer K F) :
    inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) =
      inflationToAbsolute K F ((H2mul.relBrauerEquiv K F).symm ⟨b, hb'⟩) := by
  have hE : E ≤ E ⊔ F := le_sup_left
  have hF : F ≤ E ⊔ F := le_sup_right
  have hbEF : b ∈ BrauerGroup.relBrauer K ↥(E ⊔ F) := by
    let _ : Algebra E ↥(E ⊔ F) := (IntermediateField.inclusion hE).toAlgebra
    have : IsScalarTower K E ↥(E ⊔ F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact BrauerGroup.relBrauer_le_relBrauer K E _ hb
  rw [inflationToAbsolute_symm_relBrauerEquiv_of_le hE b hb hbEF,
    inflationToAbsolute_symm_relBrauerEquiv_of_le hF b hb' hbEF]

end Galois

end Main

section SepClosure

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

theorem BrauerGroup.exists_finiteGalois_mem_relBrauer (b : BrauerGroup.{u, u} K) :
    ∃ E : FiniteGaloisIntermediateField K Ks, b ∈ BrauerGroup.relBrauer K E := by
  obtain ⟨L, _, _, _, _, hb⟩ := BrauerGroup.exists_mem_relBrauer b
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  let σ : L →ₐ[K] Ks := IsSepClosed.lift
  let e : L ≃ₐ[K] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  let _ : Algebra L σ.fieldRange := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K L σ.fieldRange :=
    IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  have : FiniteDimensional K σ.fieldRange := e.toLinearEquiv.finiteDimensional
  have : IsGalois K σ.fieldRange := IsGalois.of_algEquiv e
  exact ⟨{ toIntermediateField := σ.fieldRange }, BrauerGroup.relBrauer_le_relBrauer K L _ hb⟩

variable (K Ks) in

def brauerToH2Fun (b : BrauerGroup.{u, u} K) : Multiplicative (cohomology (galUnits.{u} K Ks) 2) :=
  inflationToAbsolute K
    (BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b).choose.toIntermediateField
    ((H2mul.relBrauerEquiv K _).symm
      ⟨b, (BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b).choose_spec⟩)

theorem brauerToH2Fun_eq (b : BrauerGroup.{u, u} K) (E : IntermediateField K Ks)
    [FiniteDimensional K E] [IsGalois K E] (hb : b ∈ BrauerGroup.relBrauer K E) :
    brauerToH2Fun K Ks b = inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) :=
  inflationToAbsolute_symm_relBrauerEquiv_eq b _ hb

variable (K Ks) in

def brauerToH2 : BrauerGroup.{u, u} K →* Multiplicative (cohomology (galUnits.{u} K Ks) 2) where
  toFun := brauerToH2Fun K Ks
  map_one' := by
    obtain ⟨E, hE⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) (1 : BrauerGroup.{u, u} K)
    rw [brauerToH2Fun_eq 1 E.toIntermediateField hE]
    exact (map_one ((inflationToAbsolute K E.toIntermediateField).comp
      (H2mul.relBrauerEquiv K E).symm.toMonoidHom) :)
  map_mul' b b' := by
    obtain ⟨E, hb⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b
    obtain ⟨E', hb'⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b'
    let F := E ⊔ E'
    have hbF : b ∈ BrauerGroup.relBrauer K F := by
      let _ : Algebra E F := (IntermediateField.inclusion
        (le_sup_left : E.toIntermediateField ≤ F.toIntermediateField)).toAlgebra
      have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact BrauerGroup.relBrauer_le_relBrauer K E F hb
    have hb'F : b' ∈ BrauerGroup.relBrauer K F := by
      let _ : Algebra E' F := (IntermediateField.inclusion
        (le_sup_right : E'.toIntermediateField ≤ F.toIntermediateField)).toAlgebra
      have : IsScalarTower K E' F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact BrauerGroup.relBrauer_le_relBrauer K E' F hb'
    rw [brauerToH2Fun_eq b F.toIntermediateField hbF, brauerToH2Fun_eq b' F.toIntermediateField hb'F,
      brauerToH2Fun_eq (b * b') F.toIntermediateField (mul_mem hbF hb'F), ← map_mul, ← map_mul]
    rfl

theorem brauerToH2_eq (b : BrauerGroup.{u, u} K) (E : IntermediateField K Ks)
    [FiniteDimensional K E] [IsGalois K E] (hb : b ∈ BrauerGroup.relBrauer K E) :
    brauerToH2 K Ks b = inflationToAbsolute K E ((H2mul.relBrauerEquiv K E).symm ⟨b, hb⟩) :=
  brauerToH2Fun_eq b E hb

theorem brauerToH2_relBrauerEquiv (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    brauerToH2 K Ks (H2mul.relBrauerEquiv K E x) = inflationToAbsolute K E x := by
  rw [brauerToH2_eq _ E (H2mul.relBrauerEquiv K E x).2]
  congr 1
  exact (H2mul.relBrauerEquiv K E).symm_apply_apply x

theorem brauerToH2_injective : Function.Injective (brauerToH2 K Ks) := by
  rw [injective_iff_map_eq_one]
  intro b hb1
  obtain ⟨E, hb⟩ := BrauerGroup.exists_finiteGalois_mem_relBrauer (Ks := Ks) b
  rw [brauerToH2_eq b E.toIntermediateField hb] at hb1
  have h := (injective_iff_map_eq_one _).1 (inflationToAbsolute_injective E.toIntermediateField) _ hb1
  rw [MulEquiv.symm_apply_eq, map_one] at h
  exact congrArg Subtype.val h

theorem brauerToH2_surjective : Function.Surjective (brauerToH2 K Ks) := by
  intro x
  obtain ⟨E, _, _, y, rfl⟩ := exists_inflationToAbsolute_eq (K := K) x
  exact ⟨_, brauerToH2_relBrauerEquiv E y⟩

variable (K Ks) in

def brauerEquivH2 : BrauerGroup.{u, u} K ≃* Multiplicative (cohomologicalBrauerGroup K Ks) :=
  MulEquiv.ofBijective (brauerToH2 K Ks) ⟨brauerToH2_injective, brauerToH2_surjective⟩

end SepClosure

end GroundTheory.Brauer

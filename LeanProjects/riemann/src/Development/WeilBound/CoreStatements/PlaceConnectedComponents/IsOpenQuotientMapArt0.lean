import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import GroundTheory.GlobalFields.GlobalReciprocity.Frobenius
import GroundTheory.GlobalFields.GlobalReciprocity.LocalSurjective
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.ArtinA
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.ArtinKer

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
open GroundTheory.LocalField GroundTheory.Global GroundTheory.Global.SemiLocal

namespace PositivityTheory.FamInh

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def art0 : Ideles E →* Gab E Ω :=
  (topologicalAbelianizationEquiv E Ω).symm.toMulEquiv.toMonoidHom.comp
    ((artinMap E Ω).comp (GroundTheory.Global.IdeleClassGroup.mk E))

theorem isOpenQuotientMap_art0 : IsOpenQuotientMap (art0 E Ω) := by
  have h1 : IsOpenQuotientMap (GroundTheory.Global.IdeleClassGroup.mk E) := QuotientGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (QuotientGroup.mk : GroundTheory.Global.IdeleClassGroup E → GroundTheory.Global.IdeleClassGroup E ⧸
      Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)) := QuotientGroup.isOpenQuotientMap_mk
  have h3 := (artinQuotientEquiv (K := E) (Ω := Ω)).toHomeomorph.isOpenQuotientMap
  have h4 := (topologicalAbelianizationEquiv E Ω).symm.toHomeomorph.isOpenQuotientMap
  exact h4.comp (h3.comp (h2.comp h1))

theorem ker_art0 : (art0 E Ω).ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  rw [← comap_connectedComponent, ← ker_artinMap (K := E) (Ω := Ω)]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker]
  exact (topologicalAbelianizationEquiv E Ω).symm.toMulEquiv.map_eq_one_iff

variable {E Ω}

def res (L : IntermediateField E Ω) [IsAbelianGalois E L] : Gab E Ω →* (L ≃ₐ[E] L) :=
  (restrictAb L (le_maximalAbelianExtension L)).comp (topologicalAbelianizationEquiv E Ω).toMulEquiv.toMonoidHom

theorem res_toAb (L : IntermediateField E Ω) [IsAbelianGalois E L] (σ : G E Ω) :
    res L (toAb E Ω σ) = AlgEquiv.restrictNormalHom L σ :=
  restrictAb_topologicalAbelianizationEquiv L (le_maximalAbelianExtension L) σ

theorem continuous_res (L : IntermediateField E Ω) [IsAbelianGalois E L] : Continuous (res L) :=
  (continuous_restrictAb L (le_maximalAbelianExtension L)).comp (topologicalAbelianizationEquiv E Ω).continuous

theorem localIdele_eq (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    localIdele E v x = IdeleGroup.finiteEmbedding v x := rfl

theorem res_art0 (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L]
    (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    res L (art0 E Ω (localIdele E v x)) = localSymbol L v x := by
  rw [← restrictAb_artinMap_finiteEmbedding L v x, localIdele_eq]
  exact congrArg (restrictAb L (le_maximalAbelianExtension L))
    ((topologicalAbelianizationEquiv E Ω).apply_symm_apply _)

omit [NumberField E] [IsAlgClosure E Ω] in
theorem continuous_toAb : Continuous (toAb E Ω) := QuotientGroup.continuous_mk

theorem mem_of_forall_res {H : Subgroup (Gab E Ω)} (hH : IsClosed (H : Set (Gab E Ω))) {g : Gab E Ω}
    (h : ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L], H ≤ (res L).ker →
      res L g = 1) : g ∈ H := by
  obtain ⟨σ, rfl⟩ := toAb_surjective g
  let H' : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H.comap (toAb E Ω), hH.preimage continuous_toAb⟩
  have hfix := InfiniteGalois.fixingSubgroup_fixedField H'
  have : σ ∈ (IntermediateField.fixedField H'.1).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hab : y ∈ maximalAbelianExtension E Ω := by
      refine IntermediateField.fixedField_le (fun τ hτ => ?_) hy
      show toAb E Ω τ ∈ H
      rw [show toAb E Ω τ = 1 from (QuotientGroup.eq_one_iff τ).2 hτ]
      exact H.one_mem
    obtain ⟨L0, _, _, hL0⟩ := exists_finite_abelian_mem hab
    let L : IntermediateField E Ω := L0 ⊓ IntermediateField.fixedField H'.1
    have : FiniteDimensional E L :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : L ≤ L0)).toLinearMap
        (IntermediateField.inclusion (inf_le_left : L ≤ L0)).injective
    have : IsAbelianGalois E L := IsAbelianGalois.of_algHom (IntermediateField.inclusion (inf_le_left : L ≤ L0))
    have h1 := h L fun a ha => by
      obtain ⟨τ, rfl⟩ := toAb_surjective a
      rw [MonoidHom.mem_ker, res_toAb, ← MonoidHom.mem_ker, L.restrictNormalHom_ker,
        IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      exact (IntermediateField.mem_fixedField_iff _ z).1 hz.2 τ ha
    rw [res_toAb, ← MonoidHom.mem_ker, L.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff] at h1
    exact h1 y ⟨hL0, hy⟩
  rw [hfix] at this
  exact this

theorem eq_of_forall_res {H H' : Subgroup (Gab E Ω)} (hH : IsClosed (H : Set (Gab E Ω)))
    (hH' : IsClosed (H' : Set (Gab E Ω)))
    (h : ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
      H ≤ (res L).ker ↔ H' ≤ (res L).ker) : H = H' :=
  le_antisymm (fun _ hg => mem_of_forall_res hH' fun L _ _ hL => (h L).2 hL hg)
    (fun _ hg => mem_of_forall_res hH fun L _ _ hL => (h L).1 hL hg)

instance : T2Space (Gab E Ω) := by
  have : T2Space (maximalAbelianExtension E Ω ≃ₐ[E] maximalAbelianExtension E Ω) := krullTopology_t2
  exact (topologicalAbelianizationEquiv E Ω).symm.toHomeomorph.t2Space

theorem isClosed_map_toAb {S : Subgroup (G E Ω)} (hS : IsClosed (S : Set (G E Ω))) :
    IsClosed ((S.map (toAb E Ω) : Subgroup (Gab E Ω)) : Set (Gab E Ω)) :=
  (hS.isCompact.image continuous_toAb).isClosed

theorem isAlgClosure_top (L : IntermediateField E Ω) : IsAlgClosure L Ω :=
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) L⟩

variable {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem ine_le_ker_iff (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L]
    {w : HeightOneSpectrum (𝓞 L)} (hw : IsPlaceOver A w) :
    (Ine (F := E) A).map (toAb E Ω) ≤ (res L).ker ↔ w.asIdeal.inertia (L ≃ₐ[E] L) = ⊥ := by
  have := isAlgClosure_top L
  constructor
  · intro h
    rw [eq_bot_iff]
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := exists_lift_ine hw hτ
    rw [← res_toAb]
    exact h ⟨σ, hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    rw [MonoidHom.mem_ker, res_toAb, ← Subgroup.mem_bot, ← h]
    exact res_mem_inertia hw hσ

theorem map_units_eq (hA : IsPlaceOver A v) :
    (unitFiltrationUnits (v.adicCompletion E) 0).map ((art0 E Ω).comp (localIdele E v)) =
      (Ine (F := E) A).map (toAb E Ω) := by
  refine eq_of_forall_res ?_ (isClosed_map_toAb (isClosed_Ine A)) fun L _ _ => ?_
  · exact ((isCompact_unitFiltrationUnits 0).image ((isOpenQuotientMap_art0 E Ω).continuous.comp
      (IdeleGroup.continuous_finiteEmbedding v))).isClosed
  · have := isAlgClosure_top L
    obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
    rw [ine_le_ker_iff L hw, inertia_eq_bot_iff v w]
    constructor
    · intro h
      refine ramificationIdx_eq_one_of_units_le_ker_localSymbol (v := v) (fun x hx => ?_) w
      rw [MonoidHom.mem_ker, ← res_art0]
      exact h ⟨x, hx, rfl⟩
    · rintro h _ ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, res_art0]
      refine units_le_ker_localSymbol L v ⟨w, hwv⟩ h ?_
      have h1 := mem_unitFiltrationUnits_zero_iff_valued.1 hx
      have h2 := mem_unitFiltrationUnits_zero_iff_valued.1 (Subgroup.inv_mem _ hx)
      exact (Submonoid.mem_units_iff _ _).2 ⟨h1.le, h2.le⟩

theorem unif_frob (hA : IsPlaceOver A v) {π : (v.adicCompletion E)ˣ} (hπ : ord (π : v.adicCompletion E) = 1)
    {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    (toAb E Ω σ)⁻¹ * art0 E Ω (localIdele E v π) ∈ (Ine (F := E) A).map (toAb E Ω) := by
  refine mem_of_forall_res (isClosed_map_toAb (isClosed_Ine A)) fun L _ _ hL => ?_
  have := isAlgClosure_top L
  obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
  rw [ine_le_ker_iff L hw] at hL
  rw [map_mul, map_inv, res_toAb, res_art0, localSymbol_eq_arithFrobAt v w ((inertia_eq_bot_iff v w).1 hL) hπ]
  have h := (res_isArithFrobAt hw hσ).mul_inv_mem_inertia
    (IsArithFrobAt.arithFrobAt (𝓞 E) (L ≃ₐ[E] L) w.asIdeal)
  rw [hL, Subgroup.mem_bot, mul_inv_eq_one] at h
  rw [h, inv_mul_cancel]

theorem closure_range_eq (hA : IsPlaceOver A v) :
    ((art0 E Ω).comp (localIdele E v)).range.topologicalClosure = (Dec (F := E) A).map (toAb E Ω) := by
  refine eq_of_forall_res (Subgroup.isClosed_topologicalClosure _) (isClosed_map_toAb (isClosed_Dec A))
    fun L _ _ => ?_
  have := isAlgClosure_top L
  obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
  constructor
  · rintro h _ ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx⟩ := exists_localSymbol_eq (v := v) ⟨w, hwv⟩ (res_mem_stabilizer hw hσ)
    rw [MonoidHom.mem_ker, res_toAb, ← hx, ← res_art0]
    exact h (Subgroup.le_topologicalClosure _ ⟨x, rfl⟩)
  · intro h
    have : T2Space (L ≃ₐ[E] L) := krullTopology_t2
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_res L))
    rintro _ ⟨x, rfl⟩
    obtain ⟨σ, hσ, e⟩ := exists_lift_dec hw (localSymbol_mem_stabilizer L v ⟨w, hwv⟩ x)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, res_art0, ← e, ← res_toAb]
    exact h ⟨σ, hσ, rfl⟩

theorem art0_unit_iff (hA : IsPlaceOver A v) (g : Gab E Ω) :
    (∃ x, IsUnitAt v x ∧ art0 E Ω (localIdele E v x) = g) ↔ g ∈ (Ine (F := E) A).map (toAb E Ω) := by
  rw [← map_units_eq hA]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, mem_unitFiltrationUnits_zero_iff_valued.2 hx, e⟩,
    fun ⟨x, hx, e⟩ => ⟨x, mem_unitFiltrationUnits_zero_iff_valued.1 hx, e⟩⟩

theorem art0_unif_iff (hA : IsPlaceOver A v) (g : Gab E Ω) :
    (∃ x, IsUnifAt v x ∧ art0 E Ω (localIdele E v x) = g) ↔
      ∃ σ : G E Ω, IsFrob (F := E) A (normV v) σ ∧ toAb E Ω σ = g := by
  obtain ⟨π, hπ, hπv⟩ := exists_ord_eq_one_valued v
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨F, hF⟩ := exists_isFrob hA
    have hu : IsUnitAt v (π⁻¹ * x) := by
      unfold IsUnitAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hπv, hx, inv_mul_cancel₀ WithZero.exp_ne_zero]
    obtain ⟨ι, hι, e⟩ := Subgroup.mul_mem _ (unif_frob hA hπ hF) ((art0_unit_iff hA _).1 ⟨_, hu, rfl⟩)
    refine ⟨F * ι, isFrob_mul_of_mem_Ine hF hι, ?_⟩
    rw [map_mul, e, map_mul, map_mul, map_inv, map_inv]
    group
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨u, hu, e⟩ := (art0_unit_iff hA _).2 (unif_frob hA hπ hσ)
    refine ⟨π * u⁻¹, ?_, ?_⟩
    · unfold IsUnifAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hπv, hu, inv_one, mul_one]
    · rw [map_mul, map_mul, map_inv, map_inv, e]
      group

theorem isGlobalArtin_inv : IsGlobalArtin (art0 E Ω)⁻¹ where
  quot := (Homeomorph.inv (Gab E Ω)).isOpenQuotientMap.comp (isOpenQuotientMap_art0 E Ω)
  ker := by
    rw [← ker_art0 E Ω]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  ine v A hA g := by
    simp only [MonoidHom.inv_apply, inv_eq_iff_eq_inv]
    rw [art0_unit_iff hA, Subgroup.inv_mem_iff]
    rfl
  frob v A hA g := by
    simp only [MonoidHom.inv_apply, map_inv, inv_eq_iff_eq_inv]
    exact art0_unif_iff hA _
  dec v A hA := by
    rw [← closure_range_eq hA]
    congr 1
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, by simp⟩

theorem globalArtin : GlobalTheory.Published.GlobalArtinReciprocity := fun E Ω _ _ _ _ _ =>
  ⟨(art0 E Ω)⁻¹, isGlobalArtin_inv⟩

end PositivityTheory.FamInh

end

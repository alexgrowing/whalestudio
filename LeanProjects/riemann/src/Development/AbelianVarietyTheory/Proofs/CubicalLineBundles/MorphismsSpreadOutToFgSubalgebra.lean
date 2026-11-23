import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Spread

section General

variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)

theorem spMap_algHom_comp {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) : spMap f.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k A) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def bcMap {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A] (f : R →ₐ[k] A) :
    pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f.toRingHom)
    (by rw [Category.assoc, spMap_algHom_comp, pullback.condition])

section
variable {R R' A : Type} [CommRing R] [CommRing R'] [CommRing A] [Algebra k R] [Algebra k R']
  [Algebra k A]

@[reassoc (attr := simp)]
theorem bcMap_fst (f : R →ₐ[k] A) : bcMap pB f ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bcMap_snd (f : R →ₐ[k] A) :
    bcMap pB f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem bcMap_comp (f : R →ₐ[k] R') (g : R' →ₐ[k] A) :
    bcMap pB g ≫ bcMap pB f = bcMap pB (g.comp f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, bcMap_fst, bcMap_fst]
  · rw [Category.assoc, bcMap_snd, bcMap_snd_assoc, bcMap_snd, ← Spec.map_comp]
    rfl

@[reassoc]
theorem bcMap_comp_of_eq (f : R →ₐ[k] R') (g : R' →ₐ[k] A) (h : R →ₐ[k] A) (e : ∀ x, g (f x) = h x) :
    bcMap pB g ≫ bcMap pB f = bcMap pB h := by
  rw [bcMap_comp, show g.comp f = h from AlgHom.ext e]

theorem bcMap_eq_id (f : R →ₐ[k] R) (e : ∀ x, f x = x) : bcMap pB f = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.id_comp]
  · rw [bcMap_snd, Category.id_comp, show f = AlgHom.id k R from AlgHom.ext e]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)

theorem bcMap_id : bcMap pB (AlgHom.id k R) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.id_comp]
  · rw [bcMap_snd, Category.id_comp]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)

theorem eq_bcMap (f : R →ₐ[k] A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom) : j = bcMap pB f := by
  apply pullback.hom_ext
  · rw [h₁, bcMap_fst]
  · rw [h₂, bcMap_snd]

theorem isPullback_bcMap (f : R →ₐ[k] A) :
    IsPullback (bcMap pB f) (pullback.snd _ _) (pullback.snd _ _) (spMap f.toRingHom) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst pB _) (v₁₃ := pB)
    (h₂₂ := spMap (algebraMap k R)) ?_ (bcMap_snd _ _) (.of_hasPullback _ _)
  rw [spMap_algHom_comp, bcMap_fst]
  exact .of_hasPullback _ _

instance isAffineHom_bcMap (f : R →ₐ[k] A) : IsAffineHom (bcMap pB f) :=
  MorphismProperty.of_isPullback (isPullback_bcMap pB f).flip inferInstance

theorem isSchemeTheoreticallyDominant_bcMap [Flat pB] (f : R →ₐ[k] A) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (bcMap pB f) := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
    (CommRingCat.ofHom f.toRingHom) hf
  exact .of_isPullback (isPullback_bcMap pB f).flip

end

variable (A : Type) [CommRing A] [Algebra k A]

def ringDiagram (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] :
    Finset A ⥤ CommRingCat.{0} where
  obj s := .of (Algebra.adjoin k (s : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom

def ringCocone (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] :
    Cocone (ringDiagram k A) where
  pt := .of A
  ι := { app s := CommRingCat.ofHom (Algebra.adjoin k (s : Set A)).val.toRingHom }

def isColimitRingCocone (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] :
    IsColimit (ringCocone k A) := by
  classical
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  exact isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : A := x
        exact ⟨({x'} : Finset A), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin k (({x'} : Finset A) : Set A)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))

def bcDiagram : (Finset A)ᵒᵖ ⥤ Scheme.{0} where
  obj s := pullback pB (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))
  map {s t} h := bcMap pB
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.unop.le)))
  map_id s := bcMap_eq_id pB _ fun _ ↦ rfl
  map_comp f g := (bcMap_comp_of_eq pB _ _ _ fun _ ↦ rfl).symm

def bcCone : Cone (bcDiagram pB A) where
  pt := pullback pB (spMap (algebraMap k A))
  π :=
    { app s := bcMap pB (Algebra.adjoin k (s.unop : Set A)).val
      naturality s t f := (Category.id_comp _).trans (bcMap_comp_of_eq pB _ _ _ fun _ ↦ rfl).symm }

def isLimitBcCone : IsLimit (bcCone pB A) := by
  classical
  let α : bcDiagram pB A ⟶ (ringDiagram k A).op ⋙ Scheme.Spec :=
    { app s := pullback.snd pB _
      naturality s t f := bcMap_snd pB _ }
  exact isLimitOfIsPullbackOfIsConnected α (bcCone pB A)
    (Scheme.Spec.mapCone (ringCocone k A).op)
    { hom := pullback.snd pB _, w s := (bcMap_snd pB _).symm }
    (fun s ↦ isPullback_bcMap pB _)
    (isLimitOfPreserves Scheme.Spec (isColimitRingCocone k A).op)

instance {s t : (Finset A)ᵒᵖ} (f : s ⟶ t) : IsAffineHom ((bcDiagram pB A).map f) :=
  isAffineHom_bcMap pB _

theorem compactSpace_bc [QuasiCompact pB] {T : Scheme.{0}} [CompactSpace T] (g : T ⟶ Sp k) :
    CompactSpace ↥(pullback pB g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd pB g)

instance [QuasiCompact pB] (s : (Finset A)ᵒᵖ) : CompactSpace ((bcDiagram pB A).obj s) :=
  compactSpace_bc pB _

instance [QuasiSeparated pB] (s : (Finset A)ᵒᵖ) : QuasiSeparatedSpace ((bcDiagram pB A).obj s) :=
  (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd pB _)).mp inferInstance

def bcStr : bcDiagram pB A ⟶ (Functor.const _).obj (Sp k) where
  app s := pullback.fst pB _ ≫ pB
  naturality s t f := by
    change bcMap pB _ ≫ pullback.fst pB _ ≫ pB = (pullback.fst pB _ ≫ pB) ≫ 𝟙 _
    rw [bcMap_fst_assoc, Category.comp_id]

variable {A} (pZ : Z ⟶ Sp k)

theorem exists_fg_comp_eq [QuasiCompact pB] [QuasiSeparated pB] [LocallyOfFinitePresentation pZ]
    (φ : pullback pB (spMap (algebraMap k A)) ⟶ Z) (hφ : φ ≫ pZ = pullback.fst _ _ ≫ pB) :
    ∃ (R : Subalgebra k A) (ψ : pullback pB (spMap (algebraMap k R)) ⟶ Z),
      R.FG ∧ ψ ≫ pZ = pullback.fst _ _ ≫ pB ∧ bcMap pB R.val ≫ ψ = φ := by
  classical
  obtain ⟨s, ψ, h₁, h₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiagram pB A) (bcStr pB A) pZ (bcCone pB A) (isLimitBcCone pB A) φ (by
      ext s
      change bcMap pB _ ≫ pullback.fst pB _ ≫ pB = φ ≫ pZ
      rw [bcMap_fst_assoc, hφ])
  exact ⟨Algebra.adjoin k (s.unop : Set A), ψ, Subalgebra.fg_adjoin_finset _, h₂, h₁⟩

theorem fg_iSup {ι : Type*} [Finite ι] {R : ι → Subalgebra k A} (hR : ∀ i, (R i).FG) :
    (⨆ i, R i).FG := by
  classical
  have := Fintype.ofFinite ι
  choose s hs using hR
  refine ⟨Finset.univ.biUnion s, ?_⟩
  simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_univ, Set.iUnion_true,
    Algebra.adjoin_iUnion, hs]

theorem exists_fg_forall_comp_eq [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (φ : ι → (pullback pB (spMap (algebraMap k A)) ⟶ Z))
    (hφ : ∀ i, φ i ≫ pZ = pullback.fst _ _ ≫ pB) (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (ψ : ι → (pullback pB (spMap (algebraMap k R)) ⟶ Z)),
      R.FG ∧ R₀ ≤ R ∧ ∀ i, ψ i ≫ pZ = pullback.fst _ _ ≫ pB ∧ bcMap pB R.val ≫ ψ i = φ i := by
  choose R ψ hR h₁ h₂ using fun i ↦ exists_fg_comp_eq pB pZ (φ i) (hφ i)
  have hle (i) : R i ≤ R₀ ⊔ ⨆ i, R i := le_sup_of_le_right (le_iSup R i)
  refine ⟨R₀ ⊔ ⨆ i, R i, fun i ↦ bcMap pB (Subalgebra.inclusion (hle i)) ≫ ψ i,
    hR₀.sup (fg_iSup hR), le_sup_left, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [Category.assoc, h₁, bcMap_fst_assoc]
  · rw [bcMap_comp_of_eq_assoc pB _ _ (R i).val fun _ ↦ rfl]
    exact h₂ i

theorem exists_fg_comp_eq_comp [QuasiCompact pB] [LocallyOfFiniteType pZ]
    (R : Subalgebra k A) (hR : R.FG) (a b : pullback pB (spMap (algebraMap k R)) ⟶ Z)
    (ha : a ≫ pZ = pullback.fst _ _ ≫ pB) (hb : b ≫ pZ = pullback.fst _ _ ≫ pB)
    (hab : bcMap pB R.val ≫ a = bcMap pB R.val ≫ b) :
    ∃ (R' : Subalgebra k A) (h : R ≤ R'), R'.FG ∧
      bcMap pB (Subalgebra.inclusion h) ≫ a = bcMap pB (Subalgebra.inclusion h) ≫ b := by
  classical
  obtain ⟨s, rfl⟩ := hR
  obtain ⟨t, f, h⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (bcDiagram pB A) (bcStr pB A) pZ (bcCone pB A) (isLimitBcCone pB A) (i := .op s) a b
    ha.symm hb.symm hab
  exact ⟨Algebra.adjoin k (t.unop : Set A), _, Subalgebra.fg_adjoin_finset _, h⟩

theorem hom_ext_bcMap [Flat pB] {R : Type} [CommRing R] [Algebra k R] (f : R →ₐ[k] A)
    (hf : Function.Injective f) {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s]
    {a b : pullback pB (spMap (algebraMap k R)) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : bcMap pB f ≫ a = bcMap pB f ≫ b) : a = b :=
  have := isSchemeTheoreticallyDominant_bcMap pB f hf
  ExtUnique.hom_ext_of_dominant s h (bcMap pB f) hab

theorem exists_fg_points [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (x : ι → (Sp A ⟶ Z)) (hx : ∀ i, x i ≫ pZ = spMap (algebraMap k A))
    (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (y : ι → (Sp R ⟶ Z)), R.FG ∧ R₀ ≤ R ∧
      ∀ i, y i ≫ pZ = spMap (algebraMap k R) ∧ spMap R.val.toRingHom ≫ y i = x i := by
  obtain ⟨R, ψ, hR, hle, h⟩ := exists_fg_forall_comp_eq (𝟙 (Sp k)) pZ
    (fun i ↦ pullback.snd _ _ ≫ x i)
    (fun i ↦ by rw [Category.assoc, hx, pullback.condition]) R₀ hR₀
  refine ⟨R, fun i ↦ inv (pullback.snd (𝟙 (Sp k)) (spMap (algebraMap k R))) ≫ ψ i, hR, hle,
    fun i ↦ ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h i).1, pullback.condition, IsIso.inv_hom_id_assoc]
  · rw [← cancel_epi (pullback.snd (𝟙 (Sp k)) (spMap (algebraMap k A))), ← bcMap_snd_assoc,
      IsIso.hom_inv_id_assoc, (h i).2]

theorem point_ext {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Injective f)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s] {a b : Sp R ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : spMap f ≫ a = spMap f ≫ b) : a = b :=
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  ExtUnique.hom_ext_of_dominant s h (spMap f) hab

open Chart

theorem dualMapR_injective {R A : Type} [CommRing R] [CommRing A] {f : R →+* A}
    (hf : Function.Injective f) : Function.Injective (dualMapR f) := by
  intro a b h
  have h₁ := congrArg TrivSqZeroExt.fst h
  have h₂ := congrArg TrivSqZeroExt.snd h
  simp only [dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h₁ h₂
  exact TrivSqZeroExt.ext (hf h₁) (hf h₂)

theorem exists_fg_tangents [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (v : ι → (Sp (DualNumber A) ⟶ Z))
    (hv : ∀ i, v i ≫ pZ = spMap (algebraMap k (DualNumber A)))
    (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (w : ι → (Sp (DualNumber R) ⟶ Z)), R.FG ∧ R₀ ≤ R ∧
      ∀ i, w i ≫ pZ = spMap (algebraMap k (DualNumber R)) ∧
        spMap (dualMapR R.val.toRingHom) ≫ w i = v i := by
  classical
  obtain ⟨T, y, ⟨s, rfl⟩, -, h⟩ := exists_fg_points pZ v hv ⊥ Subalgebra.fg_bot
  let R : Subalgebra k A := R₀ ⊔ Algebra.adjoin k
    ((s.image TrivSqZeroExt.fst ∪ s.image TrivSqZeroExt.snd : Finset A) : Set A)
  let g : DualNumber R →ₐ[k] DualNumber A :=
    { dualMapR R.val.toRingHom with
      commutes' := fun c ↦ by
        ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }
  have hg : Function.Injective g := dualMapR_injective Subtype.val_injective
  have hle : Algebra.adjoin k (s : Set (DualNumber A)) ≤ g.range := by
    refine Algebra.adjoin_le fun a ha ↦ ?_
    have h₁ : a.fst ∈ R := (le_sup_right : _ ≤ R) (Algebra.subset_adjoin (by
      simp only [Finset.coe_union, Finset.coe_image]
      exact Or.inl ⟨a, ha, rfl⟩))
    have h₂ : a.snd ∈ R := (le_sup_right : _ ≤ R) (Algebra.subset_adjoin (by
      simp only [Finset.coe_union, Finset.coe_image]
      exact Or.inr ⟨a, ha, rfl⟩))
    refine ⟨TrivSqZeroExt.inl ⟨_, h₁⟩ + TrivSqZeroExt.inr ⟨_, h₂⟩, ?_⟩
    ext <;> simp [g, dualMapR]
  let e : Algebra.adjoin k (s : Set (DualNumber A)) →ₐ[k] DualNumber R :=
    (AlgEquiv.ofInjective g hg).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have he (a) : g (e a) = a := by
    have := (AlgEquiv.ofInjective g hg).apply_symm_apply (Subalgebra.inclusion hle a)
    exact congrArg Subtype.val this
  refine ⟨R, fun i ↦ spMap e.toRingHom ≫ y i, hR₀.sup (Subalgebra.fg_adjoin_finset _),
    le_sup_left, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h i).1, spMap_algHom_comp]
  · rw [← (h i).2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext he

theorem tangent_ext {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Injective f)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s] {a b : Sp (DualNumber R) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : spMap (dualMapR f) ≫ a = spMap (dualMapR f) ≫ b) : a = b :=
  point_ext _ (dualMapR_injective hf) s h hab

end General

section Field

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)

theorem dominant_of_compatible (R : Subalgebra k A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom) :
    QuasiCompact j ∧ IsSchemeTheoreticallyDominant j := by
  obtain rfl := eq_bcMap pB R.val h₁ h₂
  exact ⟨inferInstance, isSchemeTheoreticallyDominant_bcMap pB _ Subtype.val_injective⟩

theorem hom_ext_of_compatible (R : Subalgebra k A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s]
    {a b : pullback pB (spMap (algebraMap k R)) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : j ≫ a = j ≫ b) : a = b :=
  have := (dominant_of_compatible pB R h₁ h₂).2
  ExtUnique.hom_ext_of_dominant s h j hab

end Field

end GlobalTheory.Spread

namespace GlobalTheory

theorem morphisms_spread_out_to_fg_subalgebra (k : IntermediateField ℚ ℂ) (B Z : Scheme.{0})
    (pB : B ⟶ Sp k) (pZ : Z ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] (n : ℕ)
    (φ : Fin n → (pullback pB (spMap (algebraMap k ℂ)) ⟶ Z))
    (hφ : ∀ i, φ i ≫ pZ = pullback.fst _ _ ≫ pB) (R₀ : Subalgebra k ℂ) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k ℂ) (ψ : Fin n → (pullback pB (spMap (algebraMap k R)) ⟶ Z))
      (j : pullback pB (spMap (algebraMap k ℂ)) ⟶ pullback pB (spMap (algebraMap k R))),
      R.FG ∧ R₀ ≤ R ∧ j ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom ∧
        ∀ i, ψ i ≫ pZ = pullback.fst _ _ ≫ pB ∧ j ≫ ψ i = φ i := by
  obtain ⟨R, ψ, hR, hle, h⟩ := Spread.exists_fg_forall_comp_eq pB pZ φ hφ R₀ hR₀
  exact ⟨R, ψ, Spread.bcMap pB R.val, hR, hle, Spread.bcMap_fst _ _, Spread.bcMap_snd _ _, h⟩

end GlobalTheory

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetModelOfIsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescendsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescendsStatement

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FieldModel

theorem exists_factor {k K : Type} [Field k] [Field K] (β : k →+* K) (S : Set K) (h : S ⊆ Set.range β) :
    ∃ α : Subfield.closure S →+* k, β.comp α = (Subfield.closure S).subtype := by
  have hle : Subfield.closure S ≤ β.fieldRange := Subfield.closure_le.2 h
  refine ⟨(β.rangeRestrictFieldEquiv).symm.toRingHom.comp (Subfield.inclusion hle), RingHom.ext fun x => ?_⟩
  exact congrArg Subtype.val ((β.rangeRestrictFieldEquiv).apply_symm_apply (Subfield.inclusion hle x))

theorem spMap_comp {k k₁ K : Type} [Field k] [Field k₁] [Field K] {α : k →+* k₁} {β : k₁ →+* K} {σ : k →+* K}
    (h : β.comp α = σ) : spMap β ≫ spMap α = spMap σ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem exists_baseChange {S S₁ S₀ : Scheme.{0}} {a : S₁ ⟶ S₀} {b : S ⟶ S₁} {c : S ⟶ S₀} (h : b ≫ a = c)
    {X : Over S} {X₀ : Over S₀} {φ : X.left ⟶ X₀.left} (H : IsPullback φ X.hom X₀.hom c) :
    ∃ φ₁ : X.left ⟶ ((Over.pullback a).obj X₀).left, φ₁ ≫ pullback.fst X₀.hom a = φ ∧
      IsPullback φ₁ X.hom ((Over.pullback a).obj X₀).hom b := by
  refine ⟨pullback.lift φ (X.hom ≫ b) (by rw [Category.assoc, h, H.w]), pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst X₀.hom a) (v₁₃ := X₀.hom) (h₂₂ := a) ?_
    (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
  rw [pullback.lift_fst, h]
  exact H

def HasModel {K : Type} [Field K] (X : Over (Sp K)) : Prop :=
  ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
    ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β)

variable {K : Type} [Field K]

theorem HasModel.glue {X U V W : Over (Sp K)} (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V)
    (hu : IsOpenImmersion u.left) (hv : IsOpenImmersion v.left) (h : IsPullback p.left q.left u.left v.left)
    (hc : ∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left)
    (h₁ : QuasiCompact W.hom) (h₂ : QuasiSeparated W.hom) (h₃ : LocallyOfFiniteType U.hom)
    (h₄ : LocallyOfFiniteType V.hom) (hU : HasModel U) (hV : HasModel V) (hW : HasModel W) : HasModel X := by
  classical
  obtain ⟨sU, hU⟩ := hU
  obtain ⟨sV, hV⟩ := hV
  obtain ⟨sW, hW⟩ := hW
  let k₀ := Subfield.closure ((sU ∪ sV ∪ sW : Finset K) : Set K)
  have sub : ∀ t : Finset K, t ⊆ sU ∪ sV ∪ sW → (t : Set K) ⊆ Set.range k₀.subtype := fun t ht x hx =>
    ⟨⟨x, Subfield.subset_closure (ht hx)⟩, rfl⟩
  obtain ⟨U₀, φU, HU⟩ := hU k₀ k₀.subtype (sub _ (by intro x; simp; tauto))
  obtain ⟨V₀, φV, HV⟩ := hV k₀ k₀.subtype (sub _ (by intro x; simp; tauto))
  obtain ⟨W₀, φW, HW⟩ := hW k₀ k₀.subtype (sub _ (by intro x; simp; tauto))
  obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K k₀.subtype W U W₀ U₀ φW φU HW HU h₁ h₂ h₃ p
  obtain ⟨s₂, hs₂⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K k₀.subtype W V W₀ V₀ φW φV HW HV h₁ h₂ h₄ q
  refine ⟨sU ∪ sV ∪ sW ∪ (s₁ ∪ s₂), fun k _ β hβ => ?_⟩
  rw [Finset.coe_union, Finset.coe_union s₁, Set.union_subset_iff, Set.union_subset_iff] at hβ
  obtain ⟨α, hα⟩ := exists_factor β _ hβ.1
  obtain ⟨ψU, eU, PU⟩ := exists_baseChange (spMap_comp hα) HU
  obtain ⟨ψV, eV, PV⟩ := exists_baseChange (spMap_comp hα) HV
  obtain ⟨ψW, eW, PW⟩ := exists_baseChange (spMap_comp hα) HW
  obtain ⟨p₁, hp⟩ := hs₁ k α β hα hβ.2.1 _ _ ψW _ ψU _ (.of_hasPullback _ _) (.of_hasPullback _ _) eW eU PW.w PU.w
  obtain ⟨q₁, hq⟩ := hs₂ k α β hα hβ.2.2 _ _ ψW _ ψV _ (.of_hasPullback _ _) (.of_hasPullback _ _) eW eV PW.w PV.w
  exact GlobalTheory.T.glue_models_over_subfield k K β X U V W u v p q hu hv h hc _ _ _ ψU ψV ψW PU PV PW p₁ q₁ hp hq

abbrev part (X : Over (Sp K)) (U : X.left.Opens) : Over (Sp K) := Over.mk (U.ι ≫ X.hom)

abbrev partMap (X : Over (Sp K)) {U V : X.left.Opens} (h : U ≤ V) : part X U ⟶ part X V :=
  Over.homMk (X.left.homOfLE h) (by simp)

theorem HasModel.sup (X : Over (Sp K)) [LocallyOfFiniteType X.hom] [IsSeparated X.hom] (A B : X.left.Opens)
    (hc : IsCompact ((A ⊓ B : X.left.Opens) : Set X.left))
    (hA : HasModel (part X A)) (hB : HasModel (part X B)) (hAB : HasModel (part X (A ⊓ B))) :
    HasModel (part X (A ⊔ B)) := by
  have : CompactSpace (A ⊓ B : X.left.Opens).toScheme := isCompact_iff_compactSpace.1 hc
  refine HasModel.glue (partMap X le_sup_left) (partMap X le_sup_right) (partMap X inf_le_left)
    (partMap X inf_le_right) (inferInstanceAs (IsOpenImmersion (X.left.homOfLE le_sup_left)))
    (inferInstanceAs (IsOpenImmersion (X.left.homOfLE le_sup_right)))
    (isPullback_opens_inf_le le_sup_left le_sup_right) (fun x => ?_)
    (inferInstanceAs (QuasiCompact ((A ⊓ B).ι ≫ X.hom))) (inferInstanceAs (QuasiSeparated ((A ⊓ B).ι ≫ X.hom)))
    (inferInstanceAs (LocallyOfFiniteType (A.ι ≫ X.hom))) (inferInstanceAs (LocallyOfFiniteType (B.ι ≫ X.hom)))
    hA hB hAB
  obtain ⟨x, hx | hx⟩ := x
  · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext (X.left.homOfLE_apply le_sup_left _)⟩
  · exact Or.inr ⟨⟨x, hx⟩, Subtype.ext (X.left.homOfLE_apply le_sup_right _)⟩

theorem hasModel (X : Over (Sp K)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    HasModel X := by
  have sep : IsSeparated (terminal.from X.left) := by
    rw [← terminal.comp_from X.hom]; infer_instance
  have : X.left.IsSeparated := ⟨sep⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have aff : ∀ V : X.left.Opens, IsAffineOpen V → HasModel (part X V) := fun V hV =>
    GlobalTheory.T.exists_finset_model_of_isAffine' K (part X V) hV (inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X.hom)))
  have cpt : ∀ S V : X.left.Opens, IsCompact S.carrier → IsAffineOpen V →
      IsCompact ((S ⊓ V : X.left.Opens) : Set X.left) := fun S V hS hV =>
    QuasiSeparatedSpace.inter_isCompact _ _ S.isOpen hS V.isOpen hV.isCompact
  have h₁ : ∀ S : X.left.Opens, IsCompact (S : Set X.left) → ∀ V, IsAffineOpen V → HasModel (part X (S ⊓ V)) := by
    intro S hS
    refine compact_open_induction_on (P := fun S => ∀ V, IsAffineOpen V → HasModel (part X (S ⊓ V))) S hS ?_ ?_
    · intro V _
      rw [bot_inf_eq]
      exact aff _ (isAffineOpen_bot _)
    · intro S hS U ih V hV
      have hUV : IsAffineOpen (U.1 ⊓ V) := U.2.inf hV
      have e : S ⊓ V ⊓ (U.1 ⊓ V) = S ⊓ (U.1 ⊓ V) := by
        rw [inf_assoc, inf_left_comm V, inf_idem]
      rw [inf_sup_right]
      refine HasModel.sup X _ _ ?_ (ih V hV) (aff _ hUV) ?_
      · rw [e]; exact cpt _ _ hS hUV
      · rw [e]; exact ih _ hUV
  have h₂ : HasModel (part X ⊤) := by
    refine compact_open_induction_on (P := fun S => HasModel (part X S)) ⊤ isCompact_univ
      (aff _ (isAffineOpen_bot _)) fun S hS U ih => ?_
    exact HasModel.sup X _ _ (cpt _ _ hS U.2) ih (aff _ U.2) (h₁ S hS _ U.2)
  obtain ⟨s, hs⟩ := h₂
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨X₀, φ, H⟩ := hs k β hβ
  refine ⟨X₀, X.left.topIso.inv ≫ φ, ?_⟩
  have H' : IsPullback X.left.topIso.inv X.hom (part X ⊤).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using H'.paste_horiz H

section Square

variable {S S₀ : Scheme.{0}} {c : S ⟶ S₀} {B : Over S} {B₀ : Over S₀} {φ : B.left ⟶ B₀.left}

def sq (w : φ ≫ B₀.hom = B.hom ≫ c) : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left :=
  pullback.map B.hom B.hom B₀.hom B₀.hom φ φ c w.symm w.symm

@[reassoc]
theorem sq_fst (w : φ ≫ B₀.hom = B.hom ≫ c) : sq w ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem sq_snd (w : φ ≫ B₀.hom = B.hom ≫ c) : sq w ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ :=
  pullback.lift_snd _ _ _

theorem isPullback_sq (H : IsPullback φ B.hom B₀.hom c) :
    IsPullback (sq H.w) (B ⊗ B).hom (B₀ ⊗ B₀).hom c := by
  have h : IsPullback (fst B B).left (snd B B).left B.hom B.hom := .of_hasPullback _ _
  have h₀ : IsPullback (fst B₀ B₀).left (snd B₀ B₀).left B₀.hom B₀.hom := .of_hasPullback _ _
  have h₁ : IsPullback (sq H.w) (snd B B).left (snd B₀ B₀).left φ := by
    refine IsPullback.of_right ?_ (sq_snd _) h₀
    rw [sq_fst, H.w]
    exact h.paste_horiz H
  rw [← Over.w (snd B B), ← Over.w (snd B₀ B₀)]
  exact h₁.paste_vert H

theorem sq_comp {S₁ : Scheme.{0}} {a : S₁ ⟶ S₀} {b : S ⟶ S₁} {B₁ : Over S₁} {ψ : B.left ⟶ B₁.left}
    {χ : B₁.left ⟶ B₀.left} (e : ψ ≫ χ = φ) (w : φ ≫ B₀.hom = B.hom ≫ c) (w₁ : ψ ≫ B₁.hom = B.hom ≫ b)
    (w₂ : χ ≫ B₀.hom = B₁.hom ≫ a) : sq w₁ ≫ sq w₂ = sq w := by
  apply Over.tensorObj_ext
  · change _ ≫ (fst B₀ B₀).left = _ ≫ (fst B₀ B₀).left
    rw [Category.assoc, sq_fst, sq_fst_assoc, sq_fst, e]
  · change _ ≫ (snd B₀ B₀).left = _ ≫ (snd B₀ B₀).left
    rw [Category.assoc, sq_snd, sq_snd_assoc, sq_snd, e]

theorem isPullback_unit (c : S ⟶ S₀) : IsPullback (show (𝟙_ (Over S)).left ⟶ (𝟙_ (Over S₀)).left from c)
    (𝟙_ (Over S)).hom (𝟙_ (Over S₀)).hom c :=
  IsPullback.of_vert_isIso (fst := c) (snd := 𝟙 S) (f := 𝟙 S₀) (g := c) ⟨by simp⟩

end Square

theorem bcMap_comp {S S₁ S₀ : Scheme.{0}} {a : S₁ ⟶ S₀} {b : S ⟶ S₁} {c : S ⟶ S₀} (h : b ≫ a = c) (X : Type)
    [AddCommGroup X] : SplitTorus.bcMap b X ≫ SplitTorus.bcMap a X = SplitTorus.bcMap c X := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg _ (SplitTorus.bcMap_torusFst a X)).trans
      ((SplitTorus.bcMap_torusFst b X).trans (SplitTorus.bcMap_torusFst c X).symm))
  · change _ ≫ (splitTorus S₀ X).hom = _ ≫ (splitTorus S₀ X).hom
    rw [Category.assoc, SplitTorus.bcMap_hom, SplitTorus.bcMap_hom_assoc, SplitTorus.bcMap_hom, h]

theorem exists_finite_torusExtension_of_model {k k₀ K : Type} [Field k] [Field k₀] [Field K] {σ : k →+* K}
    {α₀ : k →+* k₀} {σ₀ : k₀ →+* K} (e₀ : σ₀.comp α₀ = σ) (G : Over (Sp k)) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsSeparated G.hom]
    (T : TorusExtension ((Over.pullback (spMap σ)).obj G)) {B₀ : Over (Sp k₀)} {φ₀ : T.B.left ⟶ B₀.left}
    (H₀ : IsPullback φ₀ T.B.hom B₀.hom (spMap σ₀)) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (ρ : k₀ →+* k₁) (β : k₁ →+* K),
      β.comp α = σ → β.comp ρ = σ₀ → ρ.comp α₀ = α →
      s ⊆ Set.range β → Nonempty (TorusExtension ((Over.pullback (spMap α)).obj G)) := by
  let _ := T.grpB
  let _ := T.addCommGroup
  have := T.isAbelian.proper
  have HG := isGrpPullback_pullback G (spMap σ)
  obtain ⟨g₀, eg₀, Hg₀⟩ := exists_baseChange (X := (Over.pullback (spMap σ)).obj G) (X₀ := G)
    (spMap_comp e₀) HG.1
  have lB : LocallyOfFiniteType T.B.hom := inferInstance
  have cG : QuasiCompact ((Over.pullback (spMap σ)).obj G).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.hom _))
  have sG : QuasiSeparated ((Over.pullback (spMap σ)).obj G).hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd G.hom _))
  have lG : LocallyOfFiniteType ((Over.pullback (spMap σ)).obj G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  have pBB : IsProper (T.B ⊗ T.B).hom := inferInstanceAs (IsProper (pullback.fst T.B.hom T.B.hom ≫ T.B.hom))
  obtain ⟨sm, hm⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ (isPullback_sq H₀) H₀ inferInstance inferInstance lB μ[T.B]
  obtain ⟨si, hi⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ H₀ H₀ inferInstance inferInstance lB ι[T.B]
  obtain ⟨se, he⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ (isPullback_unit _) H₀
    (inferInstanceAs (QuasiCompact (𝟙 (Sp K)))) (inferInstanceAs (QuasiSeparated (𝟙 (Sp K)))) lB η[T.B]
  obtain ⟨sq', hq⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K σ₀ _ _ _ _ _ _ Hg₀ H₀ cG sG lB T.q
  obtain ⟨st, ht⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k K σ _ _ _ _ _ _ (SplitTorus.isPullback_bcMap (spMap σ) T.X) HG.1
    inferInstance inferInstance lG T.i
  refine ⟨sm ∪ (si ∪ (se ∪ (sq' ∪ st))), by simp, fun k₁ _ α ρ β hαβ hρ hρα hs => ?_⟩
  simp only [Set.union_subset_iff] at hs
  obtain ⟨bm, bi, be, bq, bt⟩ := hs
  obtain ⟨φ₁, eφ, H₁⟩ := exists_baseChange (spMap_comp hρ) H₀
  have P₁ : IsPullback (pullback.fst B₀.hom (spMap ρ)) ((Over.pullback (spMap ρ)).obj B₀).hom B₀.hom (spMap ρ) :=
    .of_hasPullback _ _
  have HG₁ := isGrpPullback_pullback G (spMap α)
  obtain ⟨g₁, eg₁, Hg₁⟩ := exists_baseChange (X := (Over.pullback (spMap σ)).obj G) (X₀ := G)
    (spMap_comp hαβ) HG.1
  obtain ⟨χ, eχ, Hχ⟩ := exists_baseChange (X := (Over.pullback (spMap α)).obj G) (X₀ := G)
    (spMap_comp hρα) HG₁.1
  have egχ : g₁ ≫ χ = g₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      exact ((congrArg _ eχ).trans eg₁).trans eg₀.symm
    · change _ ≫ ((Over.pullback (spMap α₀)).obj G).hom = _ ≫ ((Over.pullback (spMap α₀)).obj G).hom
      rw [Category.assoc, Hχ.w, Hg₀.w, Hg₁.w_assoc, spMap_comp hρ]
  have gp : IsGrpPullback _ ((Over.pullback (spMap α)).obj G) (spMap β) g₁ :=
    HG₁.cancel (by rw [eg₁, spMap_comp hαβ]; exact HG) Hg₁.w
  obtain ⟨m₁, hm₁⟩ := hm k₁ ρ β hρ bm _ _ (sq H₁.w) _ φ₁ _ (isPullback_sq P₁) P₁ (sq_comp eφ _ _ _) eφ
    (isPullback_sq H₁).w H₁.w
  obtain ⟨i₁, hi₁⟩ := hi k₁ ρ β hρ bi _ _ φ₁ _ φ₁ _ P₁ P₁ eφ eφ H₁.w H₁.w
  obtain ⟨e₁, he₁⟩ := he k₁ ρ β hρ be (𝟙_ _) _ (spMap β) _ φ₁ _ (isPullback_unit (spMap ρ)) P₁ (spMap_comp hρ) eφ
    (isPullback_unit (spMap β)).w H₁.w
  obtain ⟨q₁, hq₁⟩ := hq k₁ ρ β hρ bq _ _ g₁ _ φ₁ _ Hχ P₁ egχ eφ Hg₁.w H₁.w
  obtain ⟨t₁, ht₁⟩ := ht k₁ α β hαβ bt _ _ (SplitTorus.bcMap (spMap β) T.X) _ g₁ _
    (SplitTorus.isPullback_bcMap (spMap α) T.X) HG₁.1 (bcMap_comp (spMap_comp hαβ) _) eg₁
    (SplitTorus.bcMap_hom _ _) Hg₁.w
  obtain ⟨gB, ab, gpB⟩ := GlobalTheory.T.group_structure_descends_along_pullback k₁ K β T.B _ φ₁ T.isAbelian H₁ m₁ i₁ e₁ _ (sq_fst _) (sq_snd _) hm₁ hi₁ he₁
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := GlobalTheory.T.splitTorus_extension_descends_alt k₁ K β _ T.B _ _ T.X g₁ φ₁ gp gpB T.q T.i q₁ t₁ hq₁ ht₁ T.q_hom
    T.q_flat T.q_surjective T.q_quasiCompact T.i_hom T.isKernel
  exact ⟨
    { X := T.X
      free := T.free
      finite := T.finite
      B := _
      grpB := gB
      isAbelian := ab
      q := q₁
      q_hom := c₁
      q_flat := c₂
      q_surjective := c₃
      q_quasiCompact := c₄
      i := t₁
      i_hom := c₅
      isKernel := c₆ }⟩

theorem exists_finite_torusExtension_range {k K : Type} [Field k] [Field K] (σ : k →+* K) (G : Over (Sp k))
    [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsSeparated G.hom]
    (T : TorusExtension ((Over.pullback (spMap σ)).obj G)) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ →
      s ⊆ Set.range β → Nonempty (TorusExtension ((Over.pullback (spMap α)).obj G)) := by
  let _ := T.grpB
  have := T.isAbelian.proper
  obtain ⟨s₀, hs₀⟩ := hasModel T.B
  let k₀ := Subfield.closure ((s₀ : Set K) ∪ Set.range σ)
  let α₀ : k →+* k₀ := σ.codRestrict k₀ fun x => Subfield.subset_closure (Or.inr ⟨x, rfl⟩)
  have e₀ : k₀.subtype.comp α₀ = σ := rfl
  obtain ⟨B₀, φ₀, H₀⟩ := hs₀ k₀ k₀.subtype fun x hx => ⟨⟨x, Subfield.subset_closure (Or.inl hx)⟩, rfl⟩
  obtain ⟨s, hs, h⟩ := exists_finite_torusExtension_of_model e₀ G T H₀
  refine ⟨s₀ ∪ s, s₀.finite_toSet.union hs, fun k₁ _ α β hαβ hb => ?_⟩
  obtain ⟨b₀, b₁⟩ := Set.union_subset_iff.1 hb
  obtain ⟨ρ, hρ⟩ := exists_factor β ((s₀ : Set K) ∪ Set.range σ)
    (Set.union_subset b₀ (by rintro _ ⟨x, rfl⟩; exact ⟨α x, by rw [← hαβ]; rfl⟩))
  exact h k₁ α ρ β hαβ hρ (RingHom.ext fun x => β.injective
    ((congrArg (fun f => f (α₀ x)) hρ).trans (congrArg (fun f => f x) hαβ).symm)) b₁

end GlobalTheory.FieldModel

namespace GlobalTheory

theorem exists_finite_torusExtension : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : Over (Sp k)) [GrpObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → IsSeparated G.hom →
    Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k K))).obj G)) →
    ∃ k' : IntermediateField k K, FiniteDimensional k k' ∧
      Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G)) := by
  intro k K _ _ _ _ G _ _ _ _ ⟨T⟩
  obtain ⟨s, hs, h⟩ := FieldModel.exists_finite_torusExtension_range (algebraMap k K) G T
  have := hs.to_subtype
  refine ⟨IntermediateField.adjoin k s, IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  exact h _ _ (algebraMap (IntermediateField.adjoin k s) K) rfl
    fun x hx => ⟨⟨x, IntermediateField.subset_adjoin k s hx⟩, rfl⟩

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsProjOverDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SchemeDescendsToSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePoints

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusSpread

def Near {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
    (P : ∀ (K : Type) [Field K], (Sp K ⟶ S) → Prop) : Prop :=
  ∃ (V : Scheme.{0}) (π : V ⟶ S) (v : Sp k ⟶ V), v ≫ π = x ∧ LocallyOfFiniteType π ∧
    ∀ (K : Type) [Field K] (w : Sp K ⟶ V), P K (w ≫ π)

section Near

variable {S : Scheme.{0}} {k : Type} [Field k] {x : Sp k ⟶ S} {P Q : ∀ (K : Type) [Field K], (Sp K ⟶ S) → Prop}

theorem Near.mono (h : Near x P) (H : ∀ (K : Type) [Field K] (y : Sp K ⟶ S), P K y → Q K y) : Near x Q := by
  obtain ⟨V, π, v, e, hπ, h⟩ := h
  exact ⟨V, π, v, e, hπ, fun K _ w => H K _ (h K w)⟩

theorem Near.and (h : Near x P) (h' : Near x Q) : Near x fun K _ y => P K y ∧ Q K y := by
  obtain ⟨V, π, v, e, hπ, h⟩ := h
  obtain ⟨V', π', v', e', hπ', h'⟩ := h'
  refine ⟨pullback π π', pullback.fst π π' ≫ π, pullback.lift v v' (e.trans e'.symm), by
    rw [pullback.lift_fst_assoc, e], inferInstance, fun K _ w => ⟨?_, ?_⟩⟩
  · rw [← Category.assoc]; exact h K _
  · rw [pullback.condition, ← Category.assoc]; exact h' K _

theorem Near.push {V : Scheme.{0}} {π : V ⟶ S} [LocallyOfFiniteType π] {v : Sp k ⟶ V} (e : v ≫ π = x)
    (h : Near v fun K _ w => P K (w ≫ π)) : Near x P := by
  obtain ⟨V', π', v', e', hπ', h'⟩ := h
  refine ⟨V', π' ≫ π, v', by rw [← Category.assoc, e', e], inferInstance, fun K _ w => ?_⟩
  rw [← Category.assoc]; exact h' K w

theorem Near.pull {S' : Scheme.{0}} {x' : Sp k ⟶ S'} {ρ : S' ⟶ S} (e : x' ≫ ρ = x) (h : Near x P) :
    Near x' fun K _ y => P K (y ≫ ρ) := by
  obtain ⟨V, π, v, e', hπ, h⟩ := h
  refine ⟨pullback π ρ, pullback.snd π ρ, pullback.lift v x' (e'.trans e.symm), pullback.lift_snd _ _ _,
    inferInstance, fun K _ w => ?_⟩
  change P K ((w ≫ pullback.snd π ρ) ≫ ρ)
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact h K _

theorem near_opens (U : S.Opens) (hx : ∀ z, x z ∈ U) : Near x fun _ _ y => ∀ z, y z ∈ U := by
  have hr : Set.range x ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact hx z
  refine ⟨U, U.ι, IsOpenImmersion.lift U.ι x hr, IsOpenImmersion.lift_fac _ _ _, inferInstance, fun K _ w z => ?_⟩
  rw [Scheme.Hom.comp_apply]
  exact (w z).2

end Near

theorem exists_subring {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) :
    ∃ (A : Subring k) (π : Sp A ⟶ S), spMap A.subtype ≫ π = x ∧ LocallyOfFiniteType π := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x default)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have hr : Set.range x ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim z default]; exact hxU
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec x hr)
  have : IsClosedImmersion (spMap ρ.hom.rangeRestrict) :=
    IsClosedImmersion.spec_of_surjective _ ρ.hom.rangeRestrict_surjective
  refine ⟨ρ.hom.range, spMap ρ.hom.rangeRestrict ≫ hU.fromSpec, ?_, inferInstance⟩
  rw [← Category.assoc, ← Spec.map_comp, ← IsOpenImmersion.lift_fac hU.fromSpec x hr, ← hρ]
  rfl

theorem exists_adjoin {k : Type} [Field k] (A₀ : Subring k) (F : Finset k) :
    ∃ (A : Subring k) (h : A₀ ≤ A), (F : Set k) ⊆ A ∧ LocallyOfFiniteType (spMap (Subring.inclusion h)) := by
  refine ⟨(Algebra.adjoin A₀ (F : Set k)).toSubring, fun a ha => (Algebra.adjoin A₀ (F : Set k)).algebraMap_mem ⟨a, ha⟩,
    Algebra.subset_adjoin, ?_⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have : Algebra.FiniteType A₀ (Algebra.adjoin A₀ (F : Set k)) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset F)
  exact RingHom.finiteType_algebraMap.2 this

theorem exists_finset_le {k : Type} [Field k] (R : Subring k) (h : Algebra.FiniteType ℤ R) :
    ∃ F : Finset k, ∀ A : Subring k, (F : Set k) ⊆ A → R ≤ A := by
  classical
  obtain ⟨s, hs⟩ := h.out
  refine ⟨s.image R.subtype, fun A hA x hx => ?_⟩
  have H (x : R) : (x : k) ∈ A := by
    have hx : x ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hA (by simpa using hx)
    | algebraMap r => simp
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | mul x y _ _ hx hy => exact A.mul_mem hx hy
  exact H ⟨x, hx⟩

theorem exists_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] {a : S₂ ⟶ S₁} {b : S₁ ⟶ S} {c : S₂ ⟶ S} (e : a ≫ b = c) {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G b φ) (h₂ : IsGrpPullback G₂ G c ψ) :
    ∃ χ : G₂.left ⟶ G₁.left, χ ≫ φ = ψ ∧ IsGrpPullback G₂ G₁ a χ := by
  subst e
  have w : ψ ≫ G.hom = (G₂.hom ≫ a) ≫ b := by rw [h₂.1.w, Category.assoc]
  exact ⟨h₁.1.lift _ _ w, h₁.1.lift_fst _ _ w,
    IsGrpPullback.cancel h₁ (h₂.congr rfl (h₁.1.lift_fst _ _ w).symm) (h₁.1.lift_snd _ _ w)⟩

theorem mem_nhds_of_isConstructible {Z : Type*} [TopologicalSpace Z] {ξ : Z} (hξ : IsGenericPoint ξ Set.univ)
    {s : Set Z} (hs : IsConstructible s) : (ξ ∈ s → s ∈ 𝓝 ξ) ∧ (ξ ∉ s → sᶜ ∈ 𝓝 ξ) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    refine ⟨hU.mem_nhds, fun h => ?_⟩
    have : U = ∅ := by
      by_contra hne
      exact h ((hξ.mem_open_set_iff hU).2 (by simpa using Set.nonempty_iff_ne_empty.2 hne))
    simp [this]
  | union s _ t _ hs ht =>
    refine ⟨fun h => h.elim (fun h => Filter.mem_of_superset (hs.1 h) Set.subset_union_left)
      (fun h => Filter.mem_of_superset (ht.1 h) Set.subset_union_right), fun h => ?_⟩
    rw [Set.compl_union]
    exact Filter.inter_mem (hs.2 fun h' => h (Or.inl h')) (ht.2 fun h' => h (Or.inr h'))
  | compl s _ hs => exact ⟨hs.2, fun h => by rw [compl_compl]; exact hs.1 (not_not.1 h)⟩

theorem isGenericPoint_spMap {A k : Type} [CommRing A] [Field k] (f : A →+* k) (hf : Function.Injective f)
    (z : Sp k) : IsGenericPoint (spMap f z) Set.univ := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom f) hf
  have h : DenseRange (spMap f) := (spMap f).denseRange
  have e : Set.range (spMap f) = {spMap f z} := by
    ext y
    exact ⟨by rintro ⟨z', rfl⟩; rw [Subsingleton.elim z' z]; rfl, by rintro rfl; exact ⟨z, rfl⟩⟩
  rw [IsGenericPoint, ← e]
  exact h.closure_range

theorem near_of_isConstructible {k : Type} [Field k] (A : Subring k) {C : Set (Sp A)} (hC : IsConstructible C)
    (h : spMap A.subtype default ∈ C) : Near (spMap A.subtype) fun _ _ y => ∀ z, y z ∈ C := by
  obtain ⟨U, hU, hUo, hx⟩ := mem_nhds_iff.1
    ((mem_nhds_of_isConstructible (isGenericPoint_spMap A.subtype A.subtype_injective default) hC).1 h)
  exact (near_opens ⟨U, hUo⟩ fun z => by rw [Subsingleton.elim z default]; exact hx).mono
    fun K _ y hy z => hU (hy z)

theorem near_surjective {k : Type} [Field k] (A : Subring k) {P Q P' Q' : Scheme.{0}} (c : P ⟶ Q) (s : Q ⟶ Sp A)
    [LocallyOfFinitePresentation c] [QuasiCompact c] [LocallyOfFinitePresentation s] [QuasiCompact s]
    [QuasiSeparated s] {F : P' ⟶ P} {c' : P' ⟶ Q'} {β : Q' ⟶ Q} {s' : Q' ⟶ Sp k}
    (h : IsPullback β s' s (spMap A.subtype)) (w : F ≫ c = c' ≫ β) [Surjective c'] :
    Near (spMap A.subtype) fun _ _ y => ∀ b : Q, s b ∈ Set.range y → b ∈ Set.range c := by
  have : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace s
  have : QuasiSeparatedSpace Q := (quasiSeparated_iff_quasiSeparatedSpace s).1 inferInstance
  have h₁ : IsConstructible (Set.range c) := Set.image_univ ▸ c.isConstructible_image IsConstructible.univ
  refine (near_of_isConstructible A (s.isConstructible_image h₁.compl).compl ?_).mono ?_
  · rintro ⟨b, hb, e⟩
    obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback h b default e
    obtain ⟨g, rfl⟩ := c'.surjective b'
    exact hb ⟨F g, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩
  · rintro K _ y hy b ⟨z, hz⟩
    by_contra hb
    exact hy z ⟨b, hb, hz.symm⟩

def AbAt {S : Scheme.{0}} (B : Over S) [GrpObj B] (K : Type) [Field K] (y : Sp K ⟶ S) : Prop :=
  ∃ (B' : Over (Sp K)) (_ : GrpObj B') (p : B'.left ⟶ B.left), IsGrpPullback B' B y p ∧ IsAbelianScheme B'

theorem exists_abelian_model (k : Type) [Field k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B) :
    ∃ (R : Subring k) (B₀ : Over (Sp R)) (_ : GrpObj B₀) (φ : B.left ⟶ B₀.left), Algebra.FiniteType ℤ R ∧
      Smooth B₀.hom ∧ IsSeparated B₀.hom ∧ QuasiCompact B₀.hom ∧ IsGrpPullback B B₀ (spMap R.subtype) φ ∧
      Near (spMap R.subtype) (AbAt B₀) := by
  have hc := hB.comm
  have hs := hB.smooth
  have hpr := hB.proper
  have hg := hB.geomConnected
  obtain ⟨R₀, B₀, _, _, φ₀, -, hft₀, hs₀, hsep₀, hqc₀, H₀⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring k B ∅ hs inferInstance inferInstance
  refine ⟨R₀, B₀, _, φ₀, hft₀, hs₀, hsep₀, hqc₀, H₀, ?_⟩
  let Ω := AlgebraicClosure k
  let j : k →+* Ω := algebraMap k Ω
  have hp : IsProjOver (pullback.snd B.hom (spMap j)) := (ProjSpace.isProjBy_iff_isProjOver _).1
    (AbelianProjective.isProjBy_of_isAbelianScheme Ω ((Over.pullback (spMap j)).obj B)
      (isAbelianScheme_pullback_obj _ B hB))
  let c₀ := (j.comp R₀.subtype).rangeRestrict
  have e₀ : spMap (j.comp R₀.subtype).range.subtype ≫ spMap c₀ = spMap j ≫ spMap R₀.subtype := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have : IsClosedImmersion (spMap c₀) :=
    IsClosedImmersion.spec_of_surjective _ (j.comp R₀.subtype).rangeRestrict_surjective
  obtain ⟨F, hF⟩ := GlobalTheory.isProjOver_descends_to_subring Ω _ _ _ _ (pullback.snd B₀.hom (spMap c₀)) _
    (SpreadScheme.isPullback_lift ((IsPullback.of_hasPullback B.hom (spMap j)).paste_horiz H₀.1) _ _ e₀) hp
  obtain ⟨R₁, h₁, hF₁, hft₁⟩ := exists_adjoin (j.comp R₀.subtype).range F
  let f₁ := pullback.snd (pullback.snd B₀.hom (spMap c₀)) (spMap (Subring.inclusion h₁))
  have hp₁ : IsProjOver f₁ := hF R₁ h₁ hF₁ _ _ _ (IsPullback.of_hasPullback _ _)
  have Q₁ : IsPullback (pullback.fst _ _ ≫ pullback.fst _ _) f₁ B₀.hom (spMap (Subring.inclusion h₁) ≫ spMap c₀) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have e₁ : spMap R₁.subtype ≫ spMap (Subring.inclusion h₁) ≫ spMap c₀ = spMap j ≫ spMap R₀.subtype := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]; rfl
  have hfib : GeometricallyConnected (pullback.snd f₁ (spMap R₁.subtype)) := by
    have Q := (IsPullback.of_hasPullback f₁ (spMap R₁.subtype)).paste_horiz Q₁
    rw [e₁] at Q
    have w := Q.w.trans (Category.assoc _ _ _).symm
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_right (by rw [H₀.1.lift_fst _ _ w]; exact Q) (H₀.1.lift_snd _ _ w) H₀.1) hg
  obtain ⟨f, hf, hconn⟩ := ConnOpen.geometricallyConnected_near R₁ _ f₁ _ R₁.subtype hp₁ inferInstance hfib
  let a := algebraMap R₁ (Localization.Away f)
  have hc₂ := hconn _ a (IsLocalization.Away.algebraMap_isUnit f)
  have hp₂ : IsProper (pullback.snd f₁ (spMap a)) := projProper _ _ _ (ProjSpace.isProjOver_pullback_snd a hp₁)
  have Q₂ := (IsPullback.of_hasPullback f₁ (spMap a)).paste_horiz Q₁
  have : IsOpenImmersion (spMap a) := inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom a)))
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  generalize hρ : spMap a ≫ spMap (Subring.inclusion h₁) ≫ spMap c₀ = ρ at Q₂
  have : LocallyOfFiniteType ρ := by rw [← hρ]; infer_instance
  have hC : IsConstructible (Set.range ρ) := Set.image_univ ▸ ρ.isConstructible_image IsConstructible.univ
  have hψ : spMap (IsLocalization.Away.lift f (g := R₁.subtype) hf.isUnit : Localization.Away f →+* Ω) ≫ spMap a =
      spMap R₁.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  refine (near_of_isConstructible R₀ hC ⟨spMap (IsLocalization.Away.lift f (g := R₁.subtype) hf.isUnit :
    Localization.Away f →+* Ω) default, ?_⟩).mono fun K _ y hy => ?_
  · rw [← Scheme.Hom.comp_apply, ← hρ, reassoc_of% hψ, e₁, Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  have : Surjective (pullback.fst y ρ) := ⟨fun z => by
    rw [← Set.mem_range, Scheme.Pullback.range_fst]; exact hy z⟩
  have Q₃ := (IsPullback.of_hasPullback (pullback.snd f₁ (spMap a)) (pullback.snd y ρ)).paste_horiz Q₂
  rw [← pullback.condition] at Q₃
  have w := Q₃.w.trans (Category.assoc _ _ _).symm
  have Q₄ := IsPullback.of_right (by rw [pullback.lift_fst _ _ w]; exact Q₃) (pullback.lift_snd _ _ w)
    (IsPullback.of_hasPullback B₀.hom y)
  exact ⟨_, _, _, isGrpPullback_pullback B₀ y, inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)),
    GrpFlatDesc.isProper_of_isPullback Q₄, GrpFlatDesc.geometricallyConnected_of_isPullback Q₄⟩

theorem near_isPullback {k : Type} [Field k] (A : Subring k) {P Q T : Scheme.{0}} (c : P ⟶ Q) (s : Q ⟶ Sp A)
    [LocallyOfFinitePresentation (c ≫ s)] [QuasiCompact (c ≫ s)] [QuasiSeparated (c ≫ s)] [Flat (c ≫ s)]
    [LocallyOfFinitePresentation s] [QuasiCompact s] [IsSeparated s] {τ : T ⟶ P} {t : T ⟶ Sp k}
    (hτ : IsPullback τ t (c ≫ s) (spMap A.subtype)) (hτ' : IsPullback (τ ≫ c) t s (spMap A.subtype)) :
    Near (spMap A.subtype) fun K _ y => ∀ (T' : Scheme.{0}) (τ' : T' ⟶ P) (t' : T' ⟶ Sp K),
      IsPullback τ' t' (c ≫ s) y → IsPullback (τ' ≫ c) t' s y := by
  replace hτ : IsPullback τ t (c ≫ s) (spMap (algebraMap A k)) := hτ
  obtain ⟨R, e, hR, he, H⟩ := SpreadScheme.models_iso (k := A) (V := k) hτ hτ'
  have hc : e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c := by
    refine Spread.hom_ext_bcMap (c ≫ s) R.val Subtype.val_injective s ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition, reassoc_of% he]
    · have h₁ : (hτ.isoPullback.hom ≫ Spread.bcMap (c ≫ s) R.val) ≫ pullback.fst _ _ = τ := by
        rw [Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst]
      rw [← cancel_epi hτ.isoPullback.hom, ← Category.assoc, H _ h₁ (by
        rw [Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]), ← Category.assoc,
        ← Category.assoc, h₁]
  have : Algebra.FiniteType A R := (Subalgebra.fg_iff_finiteType _).1 hR
  refine ⟨Sp R, spMap (algebraMap A R), spMap R.val.toRingHom, Spread.spMap_algHom_comp R.val,
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 this),
    fun K _ w T' τ' t' h => ?_⟩
  have h₂ : IsPullback e.hom (pullback.snd _ _) (pullback.snd _ _) (𝟙 _) := .of_horiz_isIso ⟨by simpa using he⟩
  have h₃ := (SpreadScheme.isPullback_lift h w _ rfl).paste_horiz (h₂.paste_horiz (.of_hasPullback _ _))
  rwa [hc, pullback.lift_fst_assoc, Category.id_comp] at h₃

theorem flat_of_surjective {K : Type} [Field K] {G B : Over (Sp K)} [GrpObj G] [GrpObj B] [Smooth G.hom]
    [GeometricallyConnected G.hom] (hB : IsAbelianScheme B) (q : G ⟶ B) [IsMonHom q] [Surjective q.left]
    [QuasiCompact q.left] : Flat q.left := by
  let f := spMap (algebraMap K (AlgebraicClosure K))
  have hB' := isAbelianScheme_pullback_obj f B hB
  have := hB'.smooth
  have := hB'.geomConnected
  have : Smooth ((Over.pullback f).obj G).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : GeometricallyConnected ((Over.pullback f).obj G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
  have := grpObj_geometricallyIntegral_of_smooth _ ((Over.pullback f).obj G)
  have := grpObj_geometricallyIntegral_of_smooth _ ((Over.pullback f).obj B)
  have : IsIntegral ((Over.pullback f).obj G).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback f).obj G).hom
  have : IsIntegral ((Over.pullback f).obj B).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback f).obj B).hom
  have hq := SS.isPullback_overPullback_map_left f q
  have : Surjective ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @Surjective) hq ‹_›
  have : QuasiCompact ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hq ‹_›
  have := flat_descendsAlong_fpqc
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hq.flip
    (ExtDescent.fpqc_of_isPullback (IsPullback.of_hasPullback B.hom f))
    (SS.flat_of_isDominant_grpHom _ _ _ ((Over.pullback f).map q))

def RkAt {S : Scheme.{0}} (G : Over S) [GrpObj G] (r : ℕ) (K : Type) [Field K] (y : Sp K ⟶ S) : Prop :=
  ∀ (G' : Over (Sp K)) [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G y F →
    ∃ T' : TorusExtension G', @Module.finrank ℤ T'.X _ T'.addCommGroup.toAddCommMonoid _ = r

theorem rkAt_of_fibre {S : Scheme.{0}} {K : Type} [Field K] {y : Sp K ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] {G B : Over S} [GrpObj G] [GrpObj B] [Smooth G.hom]
    [GeometricallyConnected G.hom] (hB : AbAt B K y) (q : G ⟶ B) [IsMonHom q] [QuasiCompact q.left]
    (hs : ∀ b : B.left, B.hom b ∈ Set.range y → b ∈ Set.range q.left) (i : splitTorus S X ⟶ G) [IsMonHom i]
    (k₁ : IsPullback (SplitTorus.bcMap y X ≫ i.left) (splitTorus (Sp K) X).hom q.left (y ≫ (η[B]).left)) :
    RkAt G (Module.finrank ℤ X) K y := by
  intro G' _ F hF
  obtain ⟨B', _, p, hB, hab⟩ := hB
  obtain ⟨i', hi, -⟩ := GlobalTheory.UU.existsUnique_torusCompat hF.1 i
  have w : (F ≫ q.left) ≫ B.hom = G'.hom ≫ y := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ B' := Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq : q'.left ≫ p = F ≫ q.left := hB.1.lift_fst _ _ w
  have sq : IsPullback F q'.left q.left p := by
    refine IsPullback.of_bot ?_ hq.symm hB.1
    rw [Over.w, Over.w]; exact hF.1
  have ker : IsPullback i' (toUnit _) q' (η[B']) := by
    have e₁ : SplitTorus.bcMap y X ≫ i.left = i'.left ≫ F := GlobalTheory.UU.torusCompat_iff.1 hi
    have e₂ := GlobalTheory.UU.eSec_comp_of_isGrpPullback hB
    have w' : i'.left ≫ q'.left = (splitTorus (Sp K) X).hom ≫ (η[B']).left := by
      refine hB.1.hom_ext ?_ ?_
      · rw [Category.assoc, hq, ← Category.assoc, ← e₁, k₁.w]
        exact (congrArg (_ ≫ ·) e₂.symm).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
        exact (Category.comp_id _).symm
    rw [e₁] at k₁
    have k₂ : IsPullback i'.left (splitTorus (Sp K) X).hom q'.left (η[B']).left :=
      IsPullback.of_right (k₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp) (by simpa using e₂.symm)) w' sq
    rw [← Rosenlicht.toUnit_left] at k₂ w'
    exact IsPullback.of_map (Over.forget (Sp K)) (Over.OverMorphism.ext w') k₂
  have := GlobalTheory.UU.isMonHom_of_over_isMonHom hF hB q q' hq
  have : Surjective q'.left := ⟨fun b => by
    obtain ⟨g, hg⟩ := hs (p b) ⟨B'.hom b, by rw [← Scheme.Hom.comp_apply, ← hB.1.w, Scheme.Hom.comp_apply]⟩
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback sq g b hg
    exact ⟨z, hz⟩⟩
  have : QuasiCompact q'.left := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : Smooth G'.hom := MorphismProperty.of_isPullback (P := @Smooth) hF.1 inferInstance
  have : GeometricallyConnected G'.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hF.1 inferInstance
  exact ⟨{ X := X
           B := B'
           isAbelian := hab
           q := q'
           i := i'
           q_hom := inferInstance
           i_hom := hi.isMonHom hF
           q_flat := flat_of_surjective hab q'
           q_surjective := inferInstance
           q_quasiCompact := inferInstance
           isKernel := ker }, rfl⟩

theorem near_rkAt_of_maps {k : Type} [Field k] (A : Subring k) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {G B : Over (Sp A)} [GrpObj G] [GrpObj B] [Smooth G.hom] [IsSeparated G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom] [Smooth B.hom] [IsSeparated B.hom] [QuasiCompact B.hom]
    {G' B' : Over (Sp k)} [GrpObj G'] [GrpObj B'] {φ : G'.left ⟶ G.left} {β : B'.left ⟶ B.left}
    (hG : IsGrpPullback G' G (spMap A.subtype) φ) (hB : IsGrpPullback B' B (spMap A.subtype) β)
    (q' : G' ⟶ B') [IsMonHom q'] [Surjective q'.left] (i' : splitTorus (Sp k) X ⟶ G') [IsMonHom i']
    (hk : IsPullback i' (toUnit _) q' η[B']) (q : G ⟶ B) (hq : φ ≫ q.left = q'.left ≫ β)
    (i : splitTorus (Sp A) X ⟶ G) (hi : SplitTorus.bcMap (spMap A.subtype) X ≫ i.left = i'.left ≫ φ)
    (hab : Near (spMap A.subtype) (AbAt B)) : Near (spMap A.subtype) (RkAt G (Module.finrank ℤ X)) := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom A.subtype) A.subtype_injective
  have hT := SplitTorus.isGrpPullback_bcMap (spMap A.subtype) X
  have := ExtUnique.isMonHom_of_isGrpPullback hG hB q' q hq.symm
  have := ExtUnique.isMonHom_of_isGrpPullback hT hG i' i hi.symm
  have k₀ : IsPullback i'.left (splitTorus (Sp k) X).hom q'.left (η[B']).left := by
    have := hk.map (Over.forget _)
    rw [← Rosenlicht.toUnit_left]
    exact this
  have sq : IsPullback φ q'.left q.left β := by
    refine IsPullback.of_bot ?_ hq hB.1
    rw [Over.w, Over.w]; exact hG.1
  have k₁ := k₀.paste_horiz sq
  rw [← hi, GlobalTheory.UU.eSec_comp_of_isGrpPullback hB] at k₁
  have w : i.left ≫ q.left = (splitTorus (Sp A) X).hom ≫ (η[B]).left := by
    have : i ≫ q = toUnit _ ≫ η[B] := ExtUnique.over_hom_ext_of_isPullback hT.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, k₁.w, Rosenlicht.toUnit_left, ← Category.assoc,
        ← Category.assoc, hT.1.w])
    rw [← Rosenlicht.toUnit_left]
    exact congrArg (fun z => z.left) this
  have : LocallyOfFinitePresentation (q.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (q.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated (q.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation q.left := TangentCrit.locallyOfFinitePresentation_of_comp _ B.hom
  have : QuasiCompact q.left := .of_comp _ B.hom
  have : IsSeparated q.left := .of_comp _ B.hom
  let e : Sp A ⟶ B.left := (η[B]).left
  let c : (splitTorus (Sp A) X).left ⟶ pullback q.left e := pullback.lift _ _ w
  have c₁ : c ≫ pullback.fst _ _ = i.left := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd _ _ = (splitTorus (Sp A) X).hom := pullback.lift_snd _ _ _
  have : Smooth (c ≫ pullback.snd _ _) := by rw [c₂]; infer_instance
  have : IsAffineHom (c ≫ pullback.snd _ _) := by rw [c₂]; infer_instance
  have hiso := near_isPullback A c (pullback.snd _ _) (τ := SplitTorus.bcMap (spMap A.subtype) X)
    (t := (splitTorus (Sp k) X).hom) (by rw [c₂]; exact hT.1)
    (IsPullback.of_right (by rw [Category.assoc, c₁]; exact k₁) (by rw [Category.assoc, c₂, hT.1.w])
      (IsPullback.of_hasPullback q.left e))
  refine ((hab.and (near_surjective A q.left B.hom hB.1 hq)).and hiso).mono fun K _ y ⟨⟨h₁, h₂⟩, h₃⟩ => ?_
  refine rkAt_of_fibre h₁ q h₂ i ?_
  have := (h₃ _ _ _ (by rw [c₂]; exact SplitTorus.isPullback_bcMap y X)).paste_horiz
    (IsPullback.of_hasPullback q.left e)
  rwa [Category.assoc, c₁] at this

theorem bcMap_comp {S S₁ S₀ : Scheme.{0}} {a : S₁ ⟶ S₀} {b : S ⟶ S₁} {c : S ⟶ S₀} (h : b ≫ a = c) (X : Type)
    [AddCommGroup X] : SplitTorus.bcMap b X ≫ SplitTorus.bcMap a X = SplitTorus.bcMap c X := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg _ (SplitTorus.bcMap_torusFst a X)).trans
      ((SplitTorus.bcMap_torusFst b X).trans (SplitTorus.bcMap_torusFst c X).symm))
  · change _ ≫ (splitTorus S₀ X).hom = _ ≫ (splitTorus S₀ X).hom
    rw [Category.assoc, SplitTorus.bcMap_hom, SplitTorus.bcMap_hom_assoc, SplitTorus.bcMap_hom, h]

theorem near_rkAt {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (G : Over S) [GrpObj G] [Smooth G.hom]
    [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] {G' : Over (Sp k)} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G x φ) (T : TorusExtension G') :
    Near x (RkAt G (@Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _)) := by
  classical
  obtain @⟨X, _, _, _, B', _, hB', q', _, -, _, -, i', _, hk⟩ := T
  obtain ⟨A₀, π₀, e₀, _⟩ := exists_subring x
  obtain ⟨R, B₀, _, β₀, hft, _, _, _, hB₀, hab⟩ := exists_abelian_model k B' hB'
  obtain ⟨F, hF⟩ := exists_finset_le R hft
  obtain ⟨A₁, h₁, hF₁, _⟩ := exists_adjoin A₀ F
  have sub : ∀ {A A' : Subring k} (h : A ≤ A'), spMap A'.subtype ≫ spMap (Subring.inclusion h) = spMap A.subtype :=
    fun h => by rw [← Spec.map_comp]; rfl
  let π₁ := spMap (Subring.inclusion h₁) ≫ π₀
  have e₁ : spMap A₁.subtype ≫ π₁ = x := by rw [← Category.assoc, sub, e₀]
  have hG₁ := isGrpPullback_pullback G π₁
  have hB₁ := isGrpPullback_pullback B₀ (spMap (Subring.inclusion (hF A₁ hF₁)))
  obtain ⟨φ₁, -, hφ₁⟩ := exists_factor e₁ hG₁ hG
  obtain ⟨β₁, -, hβ₁⟩ := exists_factor (sub _) hB₁ hB₀
  let G₁ := (Over.pullback π₁).obj G
  let B₁ := (Over.pullback (spMap (Subring.inclusion (hF A₁ hF₁)))).obj B₀
  have : Smooth G₁.hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsSeparated G₁.hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : QuasiCompact G₁.hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : GeometricallyConnected G₁.hom := inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
  have : Smooth B₁.hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsSeparated B₁.hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : QuasiCompact B₁.hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have hT₁ := SplitTorus.isPullback_bcMap (spMap A₁.subtype) X
  obtain ⟨Sq, hSq⟩ := morphism_descends_to_subring k A₁ _ _ _ G'.hom G₁.hom B₁.hom φ₁ (q'.left ≫ β₁) hφ₁.1
    (by rw [Category.assoc, hβ₁.1.w, Over.w_assoc, hφ₁.1.w])
  obtain ⟨Si, hSi⟩ := morphism_descends_to_subring k A₁ _ _ _ _ (splitTorus (Sp A₁) X).hom G₁.hom _
    (i'.left ≫ φ₁) hT₁ (by rw [Category.assoc, hφ₁.1.w, Over.w_assoc, hT₁.w])
  obtain ⟨A₂, h₂, hF₂, _⟩ := exists_adjoin A₁ (Sq ∪ Si)
  rw [Finset.coe_union, Set.union_subset_iff] at hF₂
  let j := spMap (Subring.inclusion h₂)
  have hG₂ := isGrpPullback_pullback G₁ j
  have hB₂ := isGrpPullback_pullback B₁ j
  obtain ⟨φ₂, eφ, hφ₂⟩ := exists_factor (sub h₂) hG₂ hφ₁
  obtain ⟨β₂, eβ, hβ₂⟩ := exists_factor (sub h₂) hB₂ hβ₁
  have hTj := SplitTorus.isPullback_bcMap j X
  have hT₂ := SplitTorus.isPullback_bcMap (spMap A₂.subtype) X
  obtain ⟨ψq, hq₁, hq₂⟩ := hSq A₂ h₂ hF₂.1 _ _ _ φ₂ hG₂.1 eφ hφ₂.1.w
  obtain ⟨ψi, hi₁, hi₂⟩ := hSi A₂ h₂ hF₂.2 _ _ _ _ hTj (bcMap_comp (sub h₂) X) hT₂.w
  have wq := hq₂.trans hG₂.1.w
  have wi := hi₂.trans hTj.w
  have : Smooth ((Over.pullback j).obj G₁).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsSeparated ((Over.pullback j).obj G₁).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : QuasiCompact ((Over.pullback j).obj G₁).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : GeometricallyConnected ((Over.pullback j).obj G₁).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
  have : Smooth ((Over.pullback j).obj B₁).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsSeparated ((Over.pullback j).obj B₁).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : QuasiCompact ((Over.pullback j).obj B₁).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  obtain ⟨q, eq⟩ : ∃ q : (Over.pullback j).obj G₁ ⟶ (Over.pullback j).obj B₁, q.left ≫ pullback.fst _ _ = ψq :=
    ⟨Over.homMk (hB₂.1.lift _ _ wq) (hB₂.1.lift_snd _ _ wq), hB₂.1.lift_fst _ _ wq⟩
  obtain ⟨i, ei⟩ : ∃ i : splitTorus (Sp A₂) X ⟶ (Over.pullback j).obj G₁, i.left ≫ pullback.fst _ _ = ψi :=
    ⟨Over.homMk (hG₂.1.lift _ _ wi) (hG₂.1.lift_snd _ _ wi), hG₂.1.lift_fst _ _ wi⟩
  have H := near_rkAt_of_maps A₂ hφ₂ hβ₂ q' i' hk
    q (hB₂.1.hom_ext ((Category.assoc _ _ _).trans ((congrArg _ eq).trans (hq₁.trans
        ((Category.assoc _ _ _).trans (congrArg _ eβ)).symm)))
      (by rw [Category.assoc, Category.assoc, Over.w, hφ₂.1.w, hβ₂.1.w, Over.w_assoc]))
    i (hG₂.1.hom_ext ((Category.assoc _ _ _).trans ((congrArg _ ei).trans (hi₁.trans
        ((Category.assoc _ _ _).trans (congrArg _ eφ)).symm)))
      (by rw [Category.assoc, Category.assoc, Over.w, hT₂.w, hφ₂.1.w, Over.w_assoc]))
    ((hab.pull (ρ := j ≫ spMap (Subring.inclusion (hF A₁ hF₁))) (by rw [← Category.assoc, sub, sub])).mono
      fun K _ y ⟨B'', _, p, hp, ha⟩ => by
        obtain ⟨χ, -, hχ⟩ := exists_factor rfl (hB₂.comp hB₁) hp
        exact ⟨B'', _, χ, hχ, ha⟩)
  refine Near.push (π := j ≫ π₁) (v := spMap A₂.subtype) (by rw [← Category.assoc, sub, e₁])
    (H.mono fun K _ y hy G'' _ ψ hψ => ?_)
  obtain ⟨χ, -, hχ⟩ := exists_factor rfl (hG₂.comp hG₁) hψ
  exact hy G'' χ hχ

theorem exists_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S : Scheme.{0}) (f : S ⟶ X) (k : Type) [Field k] (x : Sp k ⟶ S) (T : TorusExtension ((Over.pullback (x ≫ f)).obj t.G)), ∃ (V : Scheme.{0}) (π : V ⟶ S) (v : Sp k ⟶ V), v ≫ π = x ∧ LocallyOfFiniteType π ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ V), ∃ T' : TorusExtension ((Over.pullback (w ≫ π ≫ f)).obj t.G), @Module.finrank ℤ T'.X _ T'.addCommGroup.toAddCommMonoid _ = @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ := by
  intro E _ _ _ H X t S f k _ x T
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  have := t.semi.geomConnected
  obtain ⟨V, π, v, e, hπ, h⟩ := (near_rkAt (x ≫ f) t.G (isGrpPullback_pullback _ _) T).pull (x' := x) rfl
  exact ⟨V, π, v, e, hπ, fun K _ w => h K w _ _ ((isGrpPullback_pullback _ _).congr (Category.assoc _ _ _).symm rfl)⟩

end GlobalTheory.TorusSpread

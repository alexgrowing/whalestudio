import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifSections

open Opposite

theorem isIntegral_of_iso_comp {A B C E : CommRingCat.{0}} (i : A ⟶ B) (f : B ⟶ C) (m : C ⟶ E) [IsIso i]
    [IsIso m] (h : (i ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv i ≫ (i ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv i)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (V : Z₂.Opens) (hV : IsAffineOpen V) : (ρ.app V).hom.IsIntegral := by
  have : IsAffine V.toScheme := hV
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ V)
  rw [morphismRestrict_appTop] at h
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (q : A = B), IsIso (eqToHom q) := fun q => by
    subst q; rw [eqToHom_refl]; infer_instance
  exact @isIntegral_of_iso_comp _ _ _ _ _ _ _ (hi _) (hi _) h

theorem isNormalScheme_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem exists_germ_eq {Y : Scheme.{0}} [IsIntegral Y] [GlobalTheory.IsNormalScheme Y] (y : Y) (hy : y = genericPoint Y)
    (V : Y.Opens) (hyV : y ∈ V) (t : Y.presheaf.stalk y)
    (h : ∀ x ∈ V, ∃ (W : Y.Opens) (hW : y ∈ W), x ∈ W ∧ W ≤ V ∧
      (Y.presheaf.germ W y hW).hom.IsIntegralElem t) :
    ∃ a : Γ(Y, V), Y.presheaf.germ V y hyV a = t := by
  subst hy
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV, hi⟩ := h x hx
  have hne : Nonempty W := ⟨⟨_, hW⟩⟩
  have := GlobalTheory.IsNormalScheme.isIntegrallyClosedIn_functionField (X := Y) W
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(Y, W)) (A := Y.functionField)).1 hi
  exact ⟨W, hne, s, hxW, hWV, hs⟩

theorem isoOver_top {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [GlobalTheory.IsNormalScheme Y]
    (σ : X ⟶ Y) [UniversallyClosed σ] (U : Y.Opens) [IsIso (σ ∣_ U)]
    (hU : ((σ ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) : IsoOver σ ⊤ := by
  intro V _
  have hηU : genericPoint X ∈ σ ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ U).isOpen).2 (by simpa using hU)
  have hmem : ∀ V : Y.Opens, (V : Set Y).Nonempty → σ (genericPoint X) ∈ V := by
    intro V hV
    obtain ⟨y, hyV, hyU⟩ := nonempty_preirreducible_inter V.isOpen U.isOpen hV ⟨_, hηU⟩
    obtain ⟨x, hx⟩ := (σ ∣_ U).surjective ⟨y, hyU⟩
    have hx' : σ x.1 = y := (morphismRestrict_base_coe σ U x).symm.trans (congrArg Subtype.val hx)
    have hne : ((σ ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := ⟨x.1, show σ x.1 ∈ V from hx' ▸ hyV⟩
    exact ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ V).isOpen).2 (by simpa using hne)
  have hgen : σ (genericPoint X) = genericPoint Y := by
    have h1 : σ (genericPoint X) ⤳ genericPoint Y :=
      specializes_iff_forall_open.2 fun s hs hg => hmem ⟨s, hs⟩ ⟨_, hg⟩
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hS : IsIso (σ.stalkMap (genericPoint X)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap σ U ⟨_, hηU⟩)).1
      (((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 inferInstance).2 ⟨_, hηU⟩)
  have hSb := ConcreteCategory.bijective_of_isIso (σ.stalkMap (genericPoint X))
  by_cases hV : (V : Set Y).Nonempty
  swap
  · exact isoOver_of_isIso σ (O := U) V fun y hy => (hV ⟨y, hy⟩).elim
  have hyV := hmem V hV
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a a' e => ?_, fun b => ?_⟩
  · apply germ_injective_of_isIntegral Y (σ (genericPoint X)) hyV
    apply hSb.1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, e]
  obtain ⟨t, ht⟩ := hSb.2 (X.presheaf.germ (σ ⁻¹ᵁ V) (genericPoint X) hyV b)
  obtain ⟨a, ha⟩ := exists_germ_eq (σ (genericPoint X)) hgen V hyV t fun y hy => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    have hWV' : W ≤ V := hWV
    have hηW : σ (genericPoint X) ∈ W := hmem W ⟨y, hyW⟩
    refine ⟨W, hηW, hyW, hWV', ?_⟩
    have hi := isIntegral_app σ W hW (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b)
    have h2 := RingHom.IsIntegralElem.map hi (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom
    have e1 : (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom.comp (σ.app W).hom =
        (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.germ W (σ (genericPoint X)) hηW).hom :=
      RingHom.ext fun a => (Scheme.Hom.germ_stalkMap_apply σ W _ hηW a).symm
    have e2 : X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW
        (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b) = σ.stalkMap (genericPoint X) t := by
      exact (X.presheaf.germ_res_apply (homOfLE (σ.preimage_mono hWV')) _ hηW b).trans ht.symm
    rw [e1, e2] at h2
    have h3 := RingHom.IsIntegralElem.map h2 (inv (σ.stalkMap (genericPoint X))).hom
    have e3 : (inv (σ.stalkMap (genericPoint X))).hom.comp (σ.stalkMap (genericPoint X)).hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id]; rfl
    rwa [← RingHom.comp_assoc, e3, RingHom.id_comp, ← RingHom.comp_apply, e3, RingHom.id_apply] at h3
  refine ⟨a, germ_injective_of_isIntegral X (genericPoint X) hyV ?_⟩
  rw [← Scheme.Hom.germ_stalkMap_apply, ha, ht]

theorem modification_lineBundleGlobalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ),
    SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB →
    letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  intro k _ Y _ p U D hs hp M _ B hB
  haveI := hs
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  haveI : IsProper (M.σ ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver M.proj
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI := M.iso
  have hb := (isoOver_top M.σ U M.dense.nonempty).bijective_pull (p := p) hB (W := ⊤) le_top le_top
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  rw [← H0.finrank_top M.str (B.pull M.σ), ← H0.finrank_top p B]
  exact (LinearEquiv.ofBijective _ hb).finrank_eq.symm

end GlobalTheory.ModifSections

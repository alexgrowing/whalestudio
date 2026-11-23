import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FieldPointGraph

theorem epi_spMap {K K' : Type} [Field K] [Field K'] (ι : K →+* K') : Epi (spMap ι) := by
  have : Flat (spMap ι) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ι.toAlgebra
    exact (inferInstance : Module.Flat K K')
  have : Surjective (spMap ι) := ⟨fun y => ⟨IsLocalRing.closedPoint K', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pt (K : Type) [Field K] : Sp K := IsLocalRing.closedPoint K

theorem eq_pt {K : Type} [Field K] (t : Sp K) : t = pt K := Subsingleton.elim _ _

theorem exists_eq_spMap_comp {X : Scheme.{0}} {K : Type} [Field K] (c : Sp K ⟶ X) {x : X}
    (hx : c (pt K) = x) :
    ∃ ι : X.residueField x →+* K, c = spMap ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X c).symm⟩

theorem exists_valuationRing_factor {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (φ : R →+* A)
      (ι : FractionRing A →+* K), IsLocalHom φ ∧
        ι.comp ((algebraMap A (FractionRing A)).comp φ) = f := by
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨A, inferInstance, inferInstance, inferInstance, f.codRestrict A.toSubring hA,
    IsFractionRing.lift (A := A) (g := A.subtype) Subtype.val_injective, hl, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (A := A) (g := A.subtype) Subtype.val_injective _

theorem exists_valuationRing_of_specializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (u : Sp A ⟶ X)
      (ι : FractionRing A →+* X.residueField x),
      spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ u = X.fromSpecResidueField x ∧
        (spMap (IsLocalRing.residue A) ≫ u) (pt _) = y := by
  obtain ⟨A, _, _, _, φ, ι, hl, hf⟩ := exists_valuationRing_factor
    (X.presheaf.stalkSpecializes h ≫ X.residue x).hom
  refine ⟨A, inferInstance, inferInstance, inferInstance, spMap φ ≫ X.fromSpecStalk y, ι, ?_, ?_⟩
  · have e : spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ spMap φ =
        Spec.map (X.presheaf.stalkSpecializes h ≫ X.residue x) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hf]
      rfl
    refine Eq.trans ?_ ((congrArg (· ≫ X.fromSpecStalk y) e).trans ?_)
    · simp only [Category.assoc]
    · rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      rfl
  · have e1 : (spMap (IsLocalRing.residue A)) (pt _) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    have e2 : (spMap φ) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint _ :=
      IsLocalRing.comap_closedPoint φ
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1]
    exact (congrArg (X.fromSpecStalk y) e2).trans Scheme.fromSpecStalk_closedPoint

theorem exists_section {W Q : Scheme.{0}} (r : W ⟶ Q) [IsProper r] [IsNoetherian Q]
    [GlobalTheory.IsNormalScheme Q] (G : ∀ (K : Type) [Field K], (Sp K ⟶ W) → Prop)
    (hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! c, G K c ∧ c ≫ r = z)
    (hB : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K c → G K' (spMap ι ≫ c))
    (hV : ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ W),
      G (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) →
      G (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u)) :
    ∃ s : Q ⟶ W, s ≫ r = 𝟙 Q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), G K (z ≫ s) := by

  have hD : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K' (spMap ι ≫ c) → G K c := by
    intro K K' _ _ ι c hc
    obtain ⟨d, ⟨hd, hdr⟩, -⟩ := hU K (c ≫ r)
    have e : spMap ι ≫ c = spMap ι ≫ d :=
      (hU K' (spMap ι ≫ c ≫ r)).unique ⟨hc, Category.assoc _ _ _⟩
        ⟨hB _ _ ι d hd, by rw [Category.assoc, hdr]⟩
    have := epi_spMap ι
    rwa [(cancel_epi _).mp e]
  let T : Set W := {x | G (W.residueField x) (W.fromSpecResidueField x)}
  have hT : ∀ (K : Type) [Field K] (c : Sp K ⟶ W),
      G K c ↔ c (pt K) ∈ T := by
    intro K _ c
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp c rfl
    exact ⟨fun h => hD _ _ ι _ (hι ▸ h), fun h => by rw [hι]; exact hB _ _ ι _ h⟩
  have hspec : ∀ x y : W, x ⤳ y → x ∈ T → y ∈ T := by
    intro x y h hx
    obtain ⟨A, _, _, _, u, ι, hu, hy⟩ := exists_valuationRing_of_specializes h
    have h1 := hV A u (hD _ _ ι _ (hu ▸ hx))
    rwa [hT, hy] at h1
  choose g hg hg' using fun y : Q => hU (Q.residueField y) (Q.fromSpecResidueField y)
  let γ : Q → W := fun y => g y (pt _)
  have hγT : ∀ y, γ y ∈ T := fun y => (hT _ _).mp (hg y).1
  have hγr : ∀ y, r (γ y) = y := fun y => by
    refine (Scheme.Hom.comp_apply (g y) r _).symm.trans ?_
    rw [(hg y).2]
    exact Scheme.fromSpecResidueField_apply _ _
  have hTγ : ∀ x ∈ T, x = γ (r x) := by
    intro x hx
    have hpt : (W.fromSpecResidueField x ≫ r) (pt (W.residueField x)) =
        r x := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp (K := W.residueField x) _ hpt
    have e : W.fromSpecResidueField x = spMap ι ≫ g (r x) :=
      (hU (W.residueField x) (W.fromSpecResidueField x ≫ r)).unique ⟨hx, rfl⟩
        ⟨hB _ _ ι _ (hg _).1, by rw [Category.assoc, (hg _).2, hι]⟩
    have e1 := Scheme.fromSpecResidueField_apply x (pt (W.residueField x))
    refine e1.symm.trans ?_
    rw [e, Scheme.Hom.comp_apply]
    exact congrArg (g (r x)) (eq_pt _)
  have hfin : (γ '' genericPoints Q).Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image γ
  have hsub : closure (γ '' genericPoints Q) ⊆ T := by
    intro x hx
    rw [← Set.biUnion_of_singleton (γ '' genericPoints Q), hfin.closure_biUnion] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨_, ⟨y, -, rfl⟩, hx⟩ := hx
    exact hspec _ _ (specializes_iff_mem_closure.mpr hx) (hγT y)
  have hcl : IsClosed T := by
    have hsurj : r '' closure (γ '' genericPoints Q) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← genericPoints.closure (α := Q)]
      refine closure_minimal (fun y hy => ⟨γ y, subset_closure ⟨y, hy, rfl⟩, hγr y⟩)
        (r.isClosedMap _ isClosed_closure)
    have : T = closure (γ '' genericPoints Q) := by
      refine Set.Subset.antisymm (fun x hx => ?_) hsub
      obtain ⟨x', hx', e⟩ : r x ∈ r '' closure (γ '' genericPoints Q) := hsurj ▸ Set.mem_univ _
      rwa [hTγ x hx, ← e, ← hTγ x' (hsub hx')]
    rw [this]
    exact isClosed_closure
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hcl⟩ : Closeds W)
  have hI : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hGI : ∀ (K : Type) [Field K] (c : Sp K ⟶ I.subscheme), G K (c ≫ I.subschemeι) := by
    intro K _ c
    rw [hT, ← hI, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : IsIso (I.subschemeι ≫ r) := by
    refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance
      (ReducedSubgroup.isReduced_subscheme_vanishingIdeal _) (GlobalTheory.IsNormalScheme.pred _)
      inferInstance fun K _ z => ?_
    obtain ⟨c, ⟨hc, hcr⟩, hu⟩ := hU K z
    have hker : I.subschemeι.ker ≤ c.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      refine ReducedSubgroup.vanishingIdeal_le_ker c _ ?_
      rintro _ ⟨t, rfl⟩
      rw [eq_pt t]
      exact (hT K c).mp hc
    have hl := IsClosedImmersion.lift_fac I.subschemeι c hker
    refine ⟨IsClosedImmersion.lift I.subschemeι c hker, ?_, fun d hd => ?_⟩
    · show _ ≫ _ ≫ _ = _
      rw [← Category.assoc, hl, hcr]
    · rw [← cancel_mono I.subschemeι, hl]
      exact hu _ ⟨hGI K d, (Category.assoc _ _ _).trans hd⟩
  refine ⟨inv (I.subschemeι ≫ r) ≫ I.subschemeι, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← Category.assoc]
    exact hGI K _

theorem exists_hom_of_rel : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  intro Q P S q p _ _ _ R hC hU hB hV
  obtain ⟨s, hs, hG⟩ := exists_section (pullback.fst q p)
    (fun K _ c => R K (c ≫ pullback.fst q p) (c ≫ pullback.snd q p))
    (fun K _ z => by
      obtain ⟨w, hw, hu⟩ := hU K z
      refine ⟨pullback.lift z w (hC K z w hw), ⟨?_, pullback.lift_fst _ _ _⟩, fun c hc => ?_⟩
      · rwa [pullback.lift_fst, pullback.lift_snd]
      · refine pullback.hom_ext (by rw [pullback.lift_fst, hc.2]) ?_
        rw [pullback.lift_snd]
        exact hu _ (hc.2 ▸ hc.1))
    (fun K K' _ _ ι c hc => by
      rw [Category.assoc, Category.assoc]
      exact hB K K' ι _ _ hc)
    (fun A _ _ _ u hu => by
      rw [Category.assoc, Category.assoc] at hu ⊢
      exact hV A _ _ (by simp [pullback.condition]) hu)
  refine ⟨s ≫ pullback.snd q p, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · have := hG K z
    rwa [Category.assoc, Category.assoc, hs, Category.comp_id] at this

end GlobalTheory.FieldPointGraph

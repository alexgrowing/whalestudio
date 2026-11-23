import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace

noncomputable section

namespace GlobalTheory.LBLimit

theorem lbIso_of_refinement {X : Scheme.{0}} (L N : LB X) (hL : L.IsLB) (e : N.ι → L.ι)
    (he : ∀ a, N.U a ≤ L.U (e a))
    (hg : ∀ a b (y : X), y ∈ N.U a → y ∈ N.U b →
      gm (𝟙 X) y _ (N.g a b) = gm (𝟙 X) y _ (L.g (e a) (e b))) : LBIso L N := by
  have le : ∀ p : N.ι × L.ι, (LB.div N L).U p ≤ L.U (e p.1) ⊓ L.U p.2 :=
    fun p y hy => ⟨he _ hy.1, hy.2⟩
  refine ⟨⟨fun p => res (le p) (L.g (e p.1) p.2)⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L N (𝟙 X) y p q hy)
      ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y _ hy.2 _)))).symm)
  rw [hg p.1 q.1 y hy.1.1 hy.2.1, mul_right_comm,
    gm_cocycle hL (𝟙 X) y (he _ hy.1.1) (he _ hy.2.1) hy.2.2,
    ← gm_cocycle hL (𝟙 X) y (he _ hy.1.1) hy.1.2 hy.2.2, mul_inv_cancel_right]

theorem isLB_of_germs {X : Scheme.{0}} (L : LB X) (hc : ∀ y : X, ∃ a, y ∈ L.U a)
    (hg : ∀ a b c (y : X), y ∈ L.U a → y ∈ L.U b → y ∈ L.U c →
      gm (𝟙 X) y _ (L.g a b) * gm (𝟙 X) y _ (L.g b c) = gm (𝟙 X) y _ (L.g a c)) : L.IsLB where
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self a := unit_ext fun y hy => by
    refine (gm_res (𝟙 X) y _ hy _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (hg a a a y hy hy hy)
  cocycle a b c := unit_ext fun y hy => by
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _)
      (gm_res (𝟙 X) y _ hy _))).trans (Eq.trans ?_ (gm_res (𝟙 X) y _ hy _).symm)
    exact hg a b c y hy.1.1 hy.1.2 hy.2

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, QuasiSeparatedSpace (D.obj i)]

set_option backward.isDefEq.respectTransparency false in
include hc in

theorem exists_appLE_eq {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s : Γ(X, π i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      ((π j).appLE _ _ (cone_preimage_le D π w f U)).hom t = s := by
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isLimit _ _
    (isLimitOpensCone D _ hc i U) ((π i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, ?_⟩
  have h := (congrArg (π i ⁻¹ᵁ U).topIso.hom hj.symm).trans (Iso.inv_hom_id_apply _ s)
  have e : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), (f.appLE U V e).hom (U.topIso.hom t) =
        V.topIso.hom ((f.resLE U V e).appTop t) := by
    intro X Y f U V e t
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
  exact (e _ _ _ _ t).trans h

include hc in

theorem exists_unit_eq {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s : Γ(X, π i ⁻¹ᵁ U)ˣ) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ), ∀ y : X, y ∈ π i ⁻¹ᵁ U →
      gm (π j) y (D.map f ⁻¹ᵁ U) t = gm (𝟙 X) y (π i ⁻¹ᵁ U) s := by
  obtain ⟨j, f, t, ht⟩ := exists_appLE_eq D π w hc hU s.val
  have h₁ : π j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) ≤ π j ⁻¹ᵁ (D.obj j).basicOpen t := by
    have h := X.basicOpen_of_isUnit (ht ▸ s.isUnit)
    rw [Scheme.basicOpen_appLE] at h
    rw [← Scheme.Hom.comp_preimage, w, ← h]
    exact inf_le_right
  obtain ⟨k, g, hg⟩ := exists_map_preimage_le_map_preimage D _ hc
    (QuasiCompact.isCompact_preimage (f := D.map f) _ U.2 hU) h₁
  have le : D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have hu : IsUnit (((D.map g).appLE _ _ le).hom t) := by
    refine (D.obj k).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
    refine ((D.obj k).mem_basicOpen _ y hy).1 ?_
    rw [Scheme.basicOpen_appLE]
    exact ⟨hy, hg (le hy)⟩
  refine ⟨k, g ≫ f, hu.unit, fun y hy => Units.ext ?_⟩
  have hy' := cone_preimage_le D π w (g ≫ f) U hy
  rw [gm_val _ y _ hy', gm_val (𝟙 X) y _ hy, IsUnit.unit_spec, ← ht]
  have e : (D.map g).appLE _ _ le ≫ (π k).appLE _ _ (cone_preimage_le D π w (g ≫ f) U) =
      (π j).appLE _ _ (cone_preimage_le D π w f U) := by
    simp only [Scheme.Hom.appLE_comp_appLE, w]
  rw [← e]
  exact (TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE (cone_preimage_le D π w (g ≫ f) U)) y hy _).symm

include hc in

theorem exists_refinement_of_isLimit [∀ i, CompactSpace (D.obj i)] (L : LB X) (hL : L.IsLB) :
    ∃ (j : I) (M : LB (D.obj j)) (e : M.ι → L.ι), M.IsLB ∧ (∀ a, π j ⁻¹ᵁ M.U a ≤ L.U (e a)) ∧
      ∀ a b (y : X), π j y ∈ M.U a → π j y ∈ M.U b →
        gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L.g (e a) (e b)) := by
  have loc : ∀ x : X, ∃ (V : X.Opens) (p : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U p := by
    intro x
    obtain ⟨p, hp⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hp (L.U p).isOpen
    exact ⟨V, p, hV, hx, hle⟩
  choose W p hW hx hle using loc
  obtain ⟨i, σ, V, hcov, hV⟩ := Scheme.exists_isOpenCover_and_isAffine D _ hc W
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx y⟩) hW
  have hV' : ∀ a : σ, π i ⁻¹ᵁ V a ≤ L.U (p a) := fun a => (hV a).2.ge.trans (hle a)
  have cpt : ∀ {U U' : (D.obj i).Opens}, IsCompact (U : Set (D.obj i)) → IsCompact (U' : Set (D.obj i)) →
      IsCompact ((U ⊓ U' : (D.obj i).Opens) : Set (D.obj i)) := fun {U U'} h h' =>
    QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen h U'.isOpen h'
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have l₀ : ∀ a b : σ, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L.U (p a) ⊓ L.U (p b) :=
    fun a b y hy => ⟨hV' a hy.1, hV' b hy.2⟩
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (q : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V q.1 ⊓ V q.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V q.1 ⊓ V q.2) → gm (π j) y _ t = gm (𝟙 X) y _ (L.g (p q.1) (p q.2)))
    (by
      rintro q j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V q.1 ⊓ V q.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (by
      rintro ⟨a, b⟩
      obtain ⟨j, f, t, ht⟩ := exists_unit_eq D π w hc (cpt (hV a).1.isCompact (hV b).1.isCompact)
        (res (l₀ a b) (L.g (p a) (p b)))
      exact ⟨j, f, t, fun y hy => (ht y hy).trans (gm_res (𝟙 X) y _ hy _)⟩)
  choose t ht using hj
  have l₁ : ∀ a b c, D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) ≤ D.map f ⁻¹ᵁ (V a ⊓ V b) := fun a b c _ hy => hy.1
  have l₂ : ∀ a b c, D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) ≤ D.map f ⁻¹ᵁ (V b ⊓ V c) :=
    fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) ≤ D.map f ⁻¹ᵁ (V a ⊓ V c) :=
    fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨k, g, hk⟩ := exists_common_refinement (i := j)
    (fun (q : σ × σ × σ) k g =>
      pullU (D.map g) _ (res (l₁ q.1 q.2.1 q.2.2) (t (q.1, q.2.1)) * res (l₂ q.1 q.2.1 q.2.2) (t (q.2.1, q.2.2))) =
      pullU (D.map g) _ (res (l₃ q.1 q.2.1 q.2.2) (t (q.1, q.2.2))))
    (by
      intro q k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      refine exists_pullU_eq D π w hc ?_ _ _ fun y hy => ?_
      · exact QuasiCompact.isCompact_preimage (f := D.map f) _ (V a ⊓ V b ⊓ V c).isOpen
          (cpt (cpt (hV a).1.isCompact (hV b).1.isCompact) (hV c).1.isCompact)
      · have hy' : y ∈ π i ⁻¹ᵁ (V a ⊓ V b ⊓ V c) := by
          rw [← w f]; exact hy
        refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res (π j) y _ hy _).trans (ht (a, b) y hy'.1))
          ((gm_res (π j) y _ hy _).trans (ht (b, c) y ⟨hy'.1.2, hy'.2⟩)))).trans (Eq.trans ?_
          ((gm_res (π j) y _ hy _).trans (ht (a, c) y ⟨hy'.1.1, hy'.2⟩)).symm)
        exact gm_cocycle hL (𝟙 X) y (hV' a hy'.1.1) (hV' b hy'.1.2) (hV' c hy'.2))
  have l₄ : ∀ a b, D.map (g ≫ f) ⁻¹ᵁ V a ⊓ D.map (g ≫ f) ⁻¹ᵁ V b ≤
      D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ (V a ⊓ V b)) := fun a b => le f g (V a ⊓ V b)
  let M : LB (D.obj k) := ⟨σ, fun a => D.map (g ≫ f) ⁻¹ᵁ V a,
    fun a b => res (l₄ a b) (pullU (D.map g) _ (t (a, b)))⟩
  have val : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj k) (z : Z) (a b : σ), r z ∈ M.U a → r z ∈ M.U b →
      gm r z _ (M.g a b) = gm (r ≫ D.map g) z _ (t (a, b)) :=
    fun r z a b ha hb => gm_res_pullU r (D.map g) z (l₄ a b) ⟨ha, hb⟩ _
  have pre : ∀ a, π k ⁻¹ᵁ M.U a ≤ π i ⁻¹ᵁ V a := fun a => by
    show π k ⁻¹ᵁ (D.map (g ≫ f) ⁻¹ᵁ V a) ≤ _
    rw [← Scheme.Hom.comp_preimage, w]
  refine ⟨k, M, fun a => p a.1, isLB_of_germs M (fun y => ?_) fun a b c y ha hb hc' => ?_,
    fun a => (pre a).trans (hV' a), fun a b y ha hb => ?_⟩
  · exact hcov.exists_mem (D.map (g ≫ f) y)
  · have hy : D.map g y ∈ D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) := le f g _ (show y ∈ D.map (g ≫ f) ⁻¹ᵁ
      (V a ⊓ V b ⊓ V c) from ⟨⟨ha, hb⟩, hc'⟩)
    have e := (gm_id_pullU (D.map g) y _ hy _).symm.trans
      ((congrArg (gm (𝟙 (D.obj k)) y (D.map g ⁻¹ᵁ D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c))) (hk (a, b, c))).trans
        (gm_id_pullU (D.map g) y _ hy _))
    rw [val _ y a b ha hb, val _ y b c hb hc', val _ y a c ha hc', Category.id_comp]
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (D.map g) y _ hy _)
      (gm_res (D.map g) y _ hy _))).symm.trans (e.trans (gm_res (D.map g) y _ hy _))
  · rw [val _ y a b ha hb, w g]
    exact ht (a, b) y ⟨pre a ha, pre b hb⟩

include hc in

theorem exists_lb_of_isLimit [∀ i, CompactSpace (D.obj i)] (L : LB X) (hL : L.IsLB) :
    ∃ (j : I) (M : LB (D.obj j)), M.IsLB ∧ LBIso L (M.pull (π j)) ∧
      ∀ (Y : Scheme.{0}) (r : X ⟶ Y) (q : Y ⟶ D.obj j), r ≫ q = π j → LBIso L ((M.pull q).pull r) := by
  obtain ⟨j, M, e, hM, he, hg⟩ := exists_refinement_of_isLimit D π w hc L hL
  refine ⟨j, M, hM, lbIso_of_refinement L _ hL (fun J => e (J PUnit.unit))
    (fun J y hy => he _ (mem_pull.1 hy)) fun J J' y hy hy' => ?_, fun Y r q hr => ?_⟩
  · refine (gm_pull_g M (π j) (𝟙 X) y J J' hy hy').trans ?_
    rw [Category.id_comp]
    exact hg _ _ y (mem_pull.1 hy) (mem_pull.1 hy')
  · have m : ∀ (J : ((M.pull q).pull r).ι) (y : X), y ∈ ((M.pull q).pull r).U J →
        π j y ∈ M.U (J PUnit.unit PUnit.unit) := fun J y hy => by
      rw [← hr]
      exact (mem_pull (L := M) (F := q) (x := r y)).1 (mem_pull.1 hy)
    refine lbIso_of_refinement L _ hL (fun J => e (J PUnit.unit PUnit.unit))
      (fun J y hy => he _ (m J y hy)) fun J J' y hy hy' => ?_
    refine (gm_pull_g (M.pull q) r (𝟙 X) y J J' hy hy').trans ?_
    rw [Category.id_comp]
    refine (gm_pull_g M q r y _ _ (mem_pull.1 hy) (mem_pull.1 hy')).trans ?_
    rw [hr]
    exact hg _ _ y (m J y hy) (m J' y hy')

end Limit

theorem lb_descends_to_fg_subring : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (L : LB X), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull j) := by
  intro R _ R₀ X X₀ f f₀ π _ _ L H hL
  classical
  have H' : IsPullback π f f₀ (spMap (algebraMap R₀ R)) := H
  let ρ : ∀ s : (Finset R)ᵒᵖ, X ⟶ (Spread.bcDiagram f₀ R).obj s := fun s =>
    H'.isoPullback.hom ≫ (Spread.bcCone f₀ R).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram f₀ R).map g = ρ t := fun g =>
    (Category.assoc _ _ _).trans (congrArg _ ((Spread.bcCone f₀ R).w g))
  have hc : IsLimit (schemeConeOfFamily _ ρ w) :=
    (Spread.isLimitBcCone f₀ R).ofIsoLimit (Cone.ext H'.isoPullback fun _ => rfl).symm
  obtain ⟨s, M, hM, -, h⟩ := exists_lb_of_isLimit _ ρ w hc L hL
  refine ⟨s.unop, fun R₁ hle hS X₁ f₁ π₁ j H₁ hj₁ hj₂ => ?_⟩
  have hsub : ∀ x : Algebra.adjoin R₀ (s.unop : Set R), x.1 ∈ R₁ := fun x => by
    refine Algebra.adjoin_induction (p := fun x _ => x ∈ R₁) (fun x hx => hS hx) (fun r => hle r.2)
      (fun _ _ _ _ => R₁.add_mem) (fun _ _ _ _ => R₁.mul_mem) x.2
  let φ : Algebra.adjoin R₀ (s.unop : Set R) →+* R₁ :=
    (Algebra.adjoin R₀ (s.unop : Set R)).val.toRingHom.codRestrict R₁ hsub
  let q : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s.unop : Set R)))) :=
    pullback.lift π₁ (f₁ ≫ spMap φ) (by
      rw [H₁.w, Category.assoc, spMap_comp_ring]
      rfl)
  refine ⟨M.pull q, pull_isLB hM _, h X₁ j q ?_⟩
  show j ≫ q = H'.isoPullback.hom ≫ Spread.bcMap f₀ (Algebra.adjoin R₀ (s.unop : Set R)).val
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hj₁, Category.assoc, Spread.bcMap_fst,
      IsPullback.isoPullback_hom_fst]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hj₂, Category.assoc, spMap_comp_ring,
      Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]
    rfl

end GlobalTheory.LBLimit

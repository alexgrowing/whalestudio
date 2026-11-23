import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory

section Refine

variable {Y : Scheme.{0}}

theorem exists_gen_of_refinement (L : LB Y) (hL : L.IsLB) {A : Type} (W : A → Y.Opens)
    (hW : ∀ y : Y, ∃ a, y ∈ W a) (e : A → L.ι) (he : ∀ a, W a ≤ L.U (e a)) (u : ∀ a, Γ(Y, W a)ˣ)
    (hu : ∀ a b (y : Y), y ∈ W a → y ∈ W b →
      gm (𝟙 Y) y (W a) (u a) = gm (𝟙 Y) y _ (L.g (e a) (e b)) * gm (𝟙 Y) y (W b) (u b)) :
    ∃ t : L.Gen, t.IsGen := by
  have le₁ : ∀ i a, L.U i ⊓ W a ≤ L.U i ⊓ L.U (e a) := fun i a => inf_le_inf_left _ (he a)
  let v : ∀ i a, Γ(Y, L.U i ⊓ W a)ˣ := fun i a =>
    res (le₁ i a) (L.g i (e a)) * res inf_le_right (u a)
  have hv : ∀ i a (y : Y), y ∈ L.U i ⊓ W a → gm (𝟙 Y) y (L.U i ⊓ W a) (v i a) =
      gm (𝟙 Y) y _ (L.g i (e a)) * gm (𝟙 Y) y (W a) (u a) := fun i a y hy =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))
  have glue : ∀ i, ∃ s : Γ(Y, L.U i)ˣ, ∀ a, res (inf_le_left : L.U i ⊓ W a ≤ L.U i) s = v i a := by
    intro i
    refine glue_unit (L.U i) (fun a => L.U i ⊓ W a) (fun a => inf_le_left) (fun y hy => ?_) (v i) ?_
    · obtain ⟨a, ha⟩ := hW y
      exact Opens.mem_iSup.2 ⟨a, hy, ha⟩
    · intro a b y hy
      rw [hv i a y hy.1, hv i b y hy.2, hu a b y hy.1.2 hy.2.2, ← mul_assoc,
        gm_cocycle hL (𝟙 Y) y hy.1.1 (he a hy.1.2) (he b hy.2.2)]
  choose s hs using glue
  have hs' : ∀ i a (y : Y), y ∈ L.U i ⊓ W a → gm (𝟙 Y) y (L.U i) (s i) =
      gm (𝟙 Y) y _ (L.g i (e a)) * gm (𝟙 Y) y (W a) (u a) := fun i a y hy => by
    rw [← hv i a y hy, ← hs i a]
    exact (gm_res _ y _ hy _).symm
  refine ⟨⟨s⟩, fun i j => unit_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hW y
  rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, hs' i a y ⟨hy.1, ha⟩, hs' j a y ⟨hy.2, ha⟩,
    ← mul_assoc, gm_cocycle hL (𝟙 Y) y hy.1 hy.2 (he a ha)]

theorem gm_id_pullU {X : Scheme.{0}} (F : Y ⟶ X) (y : Y) (U : X.Opens) (hy : F y ∈ U) (t : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (F ⁻¹ᵁ U) (pullU F U t) = gm F y U t :=
  (gm_pull (𝟙 Y) F y U hy t).trans (by rw [Category.id_comp])

theorem gm_res_pullU {X Z : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) {U : X.Opens} {W : Y.Opens}
    (le : W ≤ F ⁻¹ᵁ U) (hz : r z ∈ W) (t : Γ(X, U)ˣ) :
    gm r z W (res le (pullU F U t)) = gm (r ≫ F) z U t :=
  (gm_res r z le hz _).trans (gm_pull r F z U (le hz) t)

theorem gm_pullU_mul_res {X Z : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) {U : X.Opens} {W : Y.Opens}
    (le : F ⁻¹ᵁ U ≤ W) (hz : r z ∈ F ⁻¹ᵁ U) (G : Γ(X, U)ˣ) (t : Γ(Y, W)ˣ) :
    gm r z (F ⁻¹ᵁ U) (pullU F U G * res le t) = gm (r ≫ F) z U G * gm r z W t :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r F z U hz G) (gm_res r z le hz t))

end Refine

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]

theorem exists_common_refinement {i : I} {A : Type} [Finite A] (P : A → ∀ j : I, (j ⟶ i) → Prop)
    (stable : ∀ a j (f : j ⟶ i) k (g : k ⟶ j), P a j f → P a k (g ≫ f))
    (h : ∀ a, ∃ j f, P a j f) : ∃ j f, ∀ a, P a j f := by
  classical
  have key : ∀ s : Finset A, ∃ j f, ∀ a ∈ s, P a j f := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | insert a s _ ih =>
      obtain ⟨j, f, hj⟩ := ih
      obtain ⟨j', f', hj'⟩ := h a
      obtain ⟨k, g, g', hg⟩ := IsCofiltered.cospan f f'
      refine ⟨k, g ≫ f, fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [hg]; exact stable _ _ _ _ _ hj'
      · exact stable _ _ _ _ _ (hj b hb)
  have := Fintype.ofFinite A
  obtain ⟨j, f, hj⟩ := key Finset.univ
  exact ⟨j, f, fun a => hj a (Finset.mem_univ a)⟩

def schemeConeOfFamily (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
    (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) : Cone D :=
  ⟨X, π, fun _ _ f => (Category.id_comp _).trans (w f).symm⟩

variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

omit [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] in
include w in
theorem cone_preimage_le {i j : I} (f : j ⟶ i) (U : (D.obj i).Opens) :
    π i ⁻¹ᵁ U ≤ π j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, w]

set_option backward.isDefEq.respectTransparency false in
include hc in

theorem exists_appLE_π_eq {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(X, π i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      ((π j).appLE _ _ (cone_preimage_le D π w f U)).hom t = s := by
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
  obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
    (isLimitOpensCone D _ hc i U) ((π i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, ?_⟩
  have h := (congrArg (π i ⁻¹ᵁ U).topIso.hom hj).trans (Iso.inv_hom_id_apply _ s)
  have e : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), (f.appLE U V e).hom (U.topIso.hom t) =
        V.topIso.hom ((f.resLE U V e).appTop t) := by
    intro X Y f U V e t
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
  exact (e _ _ _ _ t).trans h

include hc in

theorem exists_unit_π_eq {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(X, π i ⁻¹ᵁ U)ˣ) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ), ∀ y : X, y ∈ π i ⁻¹ᵁ U →
      gm (π j) y (D.map f ⁻¹ᵁ U) t = gm (𝟙 X) y (π i ⁻¹ᵁ U) s := by
  obtain ⟨j, f, t, ht⟩ := exists_appLE_π_eq D π w hc hU s.val
  have h₁ : π j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) ≤ π j ⁻¹ᵁ (D.obj j).basicOpen t := by
    have h := X.basicOpen_of_isUnit (ht ▸ s.isUnit)
    rw [Scheme.basicOpen_appLE] at h
    rw [← Scheme.Hom.comp_preimage, w, ← h]
    exact inf_le_right
  obtain ⟨k, g, hg⟩ := exists_map_preimage_le_map_preimage D _ hc (hU.preimage (D.map f)).isCompact h₁
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

theorem exists_pullU_eq {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s t : Γ(D.obj i, U)ˣ)
    (h : ∀ y : X, π i y ∈ U → gm (π i) y U s = gm (π i) y U t) :
    ∃ (j : I) (f : j ⟶ i), pullU (D.map f) U s = pullU (D.map f) U t := by
  have h' : pullU (π i) U s = pullU (π i) U t := unit_ext fun y hy =>
    (gm_pull (𝟙 _) _ y U hy s).trans ((h y hy).trans (gm_pull (𝟙 _) _ y U hy t).symm)
  obtain ⟨j, f, hf⟩ := exists_app_map_eq_map_of_isLimit D _ hc hU s.val t.val (congrArg Units.val h')
  exact ⟨j, f, Units.ext hf⟩

include hc in

theorem exists_units_of_isLimit {i : I} [QuasiSeparatedSpace (D.obj i)] {A : Type} [Finite A]
    (V : A → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a)) (G : ∀ a b, Γ(D.obj i, V a ⊓ V b)ˣ)
    (s : ∀ a, Γ(X, π i ⁻¹ᵁ V a)ˣ)
    (hs : ∀ a b (y : X), y ∈ π i ⁻¹ᵁ V a → y ∈ π i ⁻¹ᵁ V b →
      gm (𝟙 X) y _ (s a) = gm (π i) y _ (G a b) * gm (𝟙 X) y _ (s b)) :
    ∃ (j : I) (f : j ⟶ i) (u : ∀ a, Γ(D.obj j, D.map f ⁻¹ᵁ V a)ˣ),
      ∀ a b (y : D.obj j), y ∈ D.map f ⁻¹ᵁ V a → y ∈ D.map f ⁻¹ᵁ V b →
        gm (𝟙 _) y _ (u a) = gm (D.map f) y _ (G a b) * gm (𝟙 _) y _ (u b) := by
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun a j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ V a)ˣ, ∀ y : X, y ∈ π i ⁻¹ᵁ V a →
      gm (π j) y (D.map f ⁻¹ᵁ V a) t = gm (𝟙 X) y (π i ⁻¹ᵁ V a) (s a))
    (by
      rintro a j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V a)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun a => exists_unit_π_eq D π w hc (hV a) (s a))
  choose t ht using hj
  have l₁ : ∀ a b, D.map f ⁻¹ᵁ (V a ⊓ V b) ≤ D.map f ⁻¹ᵁ V a := fun a b _ hy => hy.1
  have l₂ : ∀ a b, D.map f ⁻¹ᵁ (V a ⊓ V b) ≤ D.map f ⁻¹ᵁ V b := fun a b _ hy => hy.2
  obtain ⟨k, g, hk⟩ := exists_common_refinement (i := j)
    (fun (p : A × A) k g => pullU (D.map g) _ (res (l₁ p.1 p.2) (t p.1)) =
      pullU (D.map g) _ (pullU (D.map f) _ (G p.1 p.2) * res (l₂ p.1 p.2) (t p.2)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b⟩
      refine exists_pullU_eq D π w hc ?_ _ _ fun y hy => ?_
      · exact QuasiCompact.isCompact_preimage (f := D.map f) _ (V a ⊓ V b).isOpen
          (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen
            (hV b).isCompact)
      · have hy' : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := by
          rw [← w f]; exact hy
        refine (gm_res (π j) y (l₁ a b) hy (t a)).trans (Eq.trans ?_
          (gm_pullU_mul_res (π j) (D.map f) y (l₂ a b) hy (G a b) (t b)).symm)
        rw [ht a y hy'.1, ht b y hy'.2, w f]
        exact hs a b y hy'.1 hy'.2)
  refine ⟨k, g ≫ f, fun a => res (le f g _) (pullU (D.map g) _ (t a)), fun a b y ha hb => ?_⟩
  have hy : D.map g y ∈ D.map f ⁻¹ᵁ (V a ⊓ V b) := ⟨le f g _ ha, le f g _ hb⟩
  have val : ∀ a, y ∈ D.map (g ≫ f) ⁻¹ᵁ V a →
      gm (𝟙 (D.obj k)) y (D.map (g ≫ f) ⁻¹ᵁ V a) (res (le f g (V a)) (pullU (D.map g) _ (t a))) =
        gm (D.map g) y (D.map f ⁻¹ᵁ V a) (t a) :=
    fun a ha => (gm_res_pullU (𝟙 _) (D.map g) y (le f g (V a)) ha (t a)).trans (by rw [Category.id_comp])
  have e := (gm_id_pullU (D.map g) y _ hy _).symm.trans
    ((congrArg (gm (𝟙 (D.obj k)) y (D.map g ⁻¹ᵁ D.map f ⁻¹ᵁ (V a ⊓ V b))) (hk (a, b))).trans
      (gm_id_pullU (D.map g) y _ hy _))
  have e' := (gm_res (D.map g) y (l₁ a b) hy (t a)).symm.trans (e.trans
    (gm_pullU_mul_res (D.map g) (D.map f) y (l₂ a b) hy (G a b) (t b)))
  refine (val a ha).trans (e'.trans (congrArg₂ (· * ·) ?_ (val b hb).symm))
  rw [D.map_comp]

theorem lb_div_isLB {Y : Scheme.{0}} {M N : LB Y} (hM : M.IsLB) (hN : N.IsLB) : (LB.div N M).IsLB where
  cover := top_le_iff.1 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart hN y
    obtain ⟨j, hj⟩ := exists_chart hM y
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  g_self p := unit_ext fun y hy => by
    refine (gm_res (𝟙 Y) y _ hy _).trans ((gm_div M N (𝟙 Y) y p p ⟨hy, hy⟩).trans ?_)
    rw [gm_self hN _ y hy.1, gm_self hM _ y hy.2, map_one, inv_one, mul_one]
  cocycle p q r := unit_ext fun y hy => by
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_div M N (𝟙 Y) y p q hy.1))
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_div M N (𝟙 Y) y q r ⟨hy.1.2, hy.2⟩)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 Y) y _ hy _).trans (gm_div M N (𝟙 Y) y p r ⟨hy.1.1, hy.2⟩)).symm)
    rw [← gm_cocycle hN (𝟙 Y) y hy.1.1.1 hy.1.2.1 hy.2.1, ← gm_cocycle hM (𝟙 Y) y hy.1.1.2 hy.1.2.2 hy.2.2,
      mul_inv, mul_mul_mul_comm]

theorem gm_div_pull_g {Y Z : Scheme.{0}} (M N : LB Y) (F : Z ⟶ Y) (z : Z) (p q : N.ι × M.ι)
    (hz : F z ∈ (LB.div N M).U p ⊓ (LB.div N M).U q) :
    gm (𝟙 Z) z _ ((LB.div (N.pull F) (M.pull F)).g (fun _ => p.1, fun _ => p.2) (fun _ => q.1, fun _ => q.2)) =
      gm F z _ ((LB.div N M).g p q) := by
  refine (gm_div (M.pull F) (N.pull F) (𝟙 Z) z (fun _ => p.1, fun _ => p.2) (fun _ => q.1, fun _ => q.2)
    ⟨⟨mem_pull.2 hz.1.1, mem_pull.2 hz.1.2⟩, mem_pull.2 hz.2.1, mem_pull.2 hz.2.2⟩).trans
    (Eq.trans ?_ (gm_div M N F z p q hz).symm)
  exact congrArg₂ (· * ·) (gm_pull_g N F (𝟙 Z) z _ _ (mem_pull.2 hz.1.1) (mem_pull.2 hz.2.1))
    (congrArg (·⁻¹) (gm_pull_g M F (𝟙 Z) z _ _ (mem_pull.2 hz.1.2) (mem_pull.2 hz.2.2)))

include hc in

theorem exists_lbIso_of_isLimit {i : I} [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (M N : LB (D.obj i)) (hM : M.IsLB) (hN : N.IsLB) (h : LBIso (M.pull (π i)) (N.pull (π i))) :
    ∃ (j : I) (f : j ⟶ i), LBIso (M.pull (D.map f)) (N.pull (D.map f)) := by
  have loc : ∀ x : D.obj i, ∃ (V : (D.obj i).Opens) (p : N.ι × M.ι),
      IsAffineOpen V ∧ x ∈ V ∧ V ≤ (LB.div N M).U p := by
    intro x
    obtain ⟨p, hp⟩ := exists_chart (lb_div_isLB hM hN) x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open hp ((LB.div N M).U p).isOpen
    exact ⟨V, p, hV, hx, hle⟩
  choose V p hV hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => (V x : Set (D.obj i)))
    (fun x => (V x).isOpen.mem_nhds (hx x))
  have cov : ∀ x : D.obj i, ∃ a : σ, x ∈ V a := fun x => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  have le : ∀ {Z : Scheme.{0}} (F : Z ⟶ D.obj i) (a : D.obj i), F ⁻¹ᵁ V a ≤
      (LB.div (N.pull F) (M.pull F)).U (fun _ => (p a).1, fun _ => (p a).2) :=
    fun F a z hz => ⟨mem_pull.2 (hle a hz).1, mem_pull.2 (hle a hz).2⟩
  obtain ⟨t, ht⟩ := h
  obtain ⟨j, f, u, hu⟩ := exists_units_of_isLimit D π w hc (fun a : σ => V a) (fun a => hV a)
    (fun a b => res (inf_le_inf (hle a) (hle b)) ((LB.div N M).g (p a) (p b)))
    (fun a => res (le (π i) a) (t.s (fun _ => (p a).1, fun _ => (p a).2))) (by
      intro a b y ha hb
      have hm : (𝟙 X : X ⟶ X) y ∈
          (LB.div (N.pull (π i)) (M.pull (π i))).U (fun _ => (p a).1, fun _ => (p a).2) ⊓
          (LB.div (N.pull (π i)) (M.pull (π i))).U (fun _ => (p b).1, fun _ => (p b).2) :=
        ⟨le _ _ ha, le _ _ hb⟩
      have e := congrArg (gm (𝟙 X) y _)
        (ht (fun _ => (p a).1, fun _ => (p a).2) (fun _ => (p b).1, fun _ => (p b).2))
      refine (gm_res (𝟙 X) y _ ha _).trans ((gm_res (𝟙 X) y _ hm _).symm.trans (e.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))))
      · exact (gm_div_pull_g M N (π i) y (p a) (p b) ⟨hle a ha, hle b hb⟩).trans
          (gm_res (π i) y _ (show π i y ∈ V a ⊓ V b from ⟨ha, hb⟩) _).symm
      · exact (gm_res (𝟙 X) y _ hm _).trans (gm_res (𝟙 X) y _ hb _).symm)
  refine ⟨j, f, exists_gen_of_refinement _ (lb_div_isLB (pull_isLB hM _) (pull_isLB hN _))
    (fun a : σ => D.map f ⁻¹ᵁ V a) (fun y => cov (D.map f y))
    (fun a => (fun _ => (p a).1, fun _ => (p a).2)) (fun a => le _ a) u fun a b y ha hb => ?_⟩
  refine (hu a b y ha hb).trans (congrArg (· * _) ?_)
  exact (gm_res (D.map f) y _ (show D.map f y ∈ V a ⊓ V b from ⟨ha, hb⟩) _).trans
    (gm_div_pull_g M N (D.map f) y (p a) (p b) ⟨hle a ha, hle b hb⟩).symm

end Limit

section Tower

variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]

abbrev FGAbove (R₀ : Subalgebra k C) : Type := {R : Subalgebra k C // R.FG ∧ R₀ ≤ R}

variable {R₀ : Subalgebra k C}

theorem FGAbove.exists_ge (R S : FGAbove R₀) : ∃ T : FGAbove R₀, R ≤ T ∧ S ≤ T :=
  ⟨⟨R.1 ⊔ S.1, R.2.1.sup S.2.1, R.2.2.trans le_sup_left⟩, le_sup_left (a := R.1), le_sup_right (a := R.1)⟩

theorem FGAbove.exists_mem (h : R₀.FG) (x : C) : ∃ R : FGAbove R₀, x ∈ R.1 :=
  ⟨⟨R₀ ⊔ Algebra.adjoin k {x}, h.sup (Subalgebra.fg_def.2 ⟨{x}, Set.finite_singleton x, rfl⟩), le_sup_left⟩,
    (le_sup_right : Algebra.adjoin k {x} ≤ _) (Algebra.self_mem_adjoin_singleton k x)⟩

theorem FGAbove.isFiltered (h : R₀.FG) : IsFiltered (FGAbove R₀) :=
  have : Nonempty (FGAbove R₀) := ⟨⟨R₀, h, le_rfl⟩⟩
  have : IsDirectedOrder (FGAbove R₀) := ⟨FGAbove.exists_ge⟩
  inferInstance

theorem FGAbove.exists_ringHom (h : R₀.FG) {S : Type} [CommRing S] (φ : ∀ R : FGAbove R₀, R.1 →+* S)
    (hφ : ∀ (R T : FGAbove R₀) (hRT : R.1 ≤ T.1) (x : R.1), φ T (Subalgebra.inclusion hRT x) = φ R x) :
    ∃ ψ : C →+* S, ∀ (R : FGAbove R₀) (x : R.1), ψ x = φ R x := by
  choose P hP using FGAbove.exists_mem h
  have key : ∀ (R : FGAbove R₀) (x : C) (hx : x ∈ R.1), φ (P x) ⟨x, hP x⟩ = φ R ⟨x, hx⟩ := by
    intro R x hx
    obtain ⟨T, h₁, h₂⟩ := FGAbove.exists_ge R (P x)
    exact (hφ _ T h₂ _).symm.trans (hφ _ T h₁ ⟨x, hx⟩)
  have two : ∀ x y : C, ∃ T : FGAbove R₀, x ∈ T.1 ∧ y ∈ T.1 := fun x y => by
    obtain ⟨T, h₁, h₂⟩ := FGAbove.exists_ge (P x) (P y)
    exact ⟨T, h₁ (hP x), h₂ (hP y)⟩
  refine ⟨⟨⟨⟨fun x => φ (P x) ⟨x, hP x⟩, map_one (φ (P 1))⟩, fun x y => ?_⟩, map_zero (φ (P 0)),
    fun x y => ?_⟩, fun R x => key R x x.2⟩
  · obtain ⟨T, hx, hy⟩ := two x y
    show φ _ _ = φ _ _ * φ _ _
    rw [key T x hx, key T y hy, key T _ (mul_mem hx hy), ← map_mul]
    rfl
  · obtain ⟨T, hx, hy⟩ := two x y
    show φ _ _ = φ _ _ + φ _ _
    rw [key T x hx, key T y hy, key T _ (add_mem hx hy), ← map_add]
    rfl

theorem spMap_comp_ring {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A')
    (g : A' →+* A'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

variable {B : Scheme.{0}} (pB : B ⟶ Sp k)

def baseChangeMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] (f : A →ₐ[k] A') :
    pullback pB (spMap (algebraMap k A')) ⟶ pullback pB (spMap (algebraMap k A)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f.toRingHom) (by
    rw [pullback.condition, Category.assoc, spMap_comp_ring]
    congr 2
    exact f.comp_algebraMap.symm)

section
variable {A A' A'' : Type} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [CommRing A''] [Algebra k A'']

@[reassoc]
theorem baseChangeMap_fst (f : A →ₐ[k] A') :
    baseChangeMap pB f ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc]
theorem baseChangeMap_snd (f : A →ₐ[k] A') :
    baseChangeMap pB f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom := pullback.lift_snd _ _ _

theorem baseChangeMap_comp (f : A →ₐ[k] A') (g : A' →ₐ[k] A'') :
    baseChangeMap pB g ≫ baseChangeMap pB f = baseChangeMap pB (g.comp f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeMap_fst, baseChangeMap_fst, baseChangeMap_fst]
  · rw [Category.assoc, baseChangeMap_snd, baseChangeMap_snd_assoc, baseChangeMap_snd, spMap_comp_ring]
    rfl

theorem baseChangeMap_id : baseChangeMap pB (AlgHom.id k A) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [baseChangeMap_fst, Category.id_comp]
  · rw [baseChangeMap_snd, Category.id_comp]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)

theorem isAffineHom_baseChangeMap (f : A →ₐ[k] A') : IsAffineHom (baseChangeMap pB f) := by
  have : IsAffineHom (pullback.fst pB (spMap (algebraMap k A))) :=
    (isAffineHom_isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsAffineHom (baseChangeMap pB f ≫ pullback.fst _ _) := by
    rw [baseChangeMap_fst]
    exact (isAffineHom_isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  exact IsAffineHom.of_comp _ (pullback.fst _ _)

end

variable (R₀) in

def baseChangeDiagram : (FGAbove R₀)ᵒᵖ ⥤ Scheme.{0} where
  obj R := pullback pB (spMap (algebraMap k R.unop.1))
  map {R T} f := baseChangeMap pB (Subalgebra.inclusion (show T.unop.1 ≤ R.unop.1 from leOfHom f.unop))
  map_id _ := baseChangeMap_id pB
  map_comp {R S T} f g := (baseChangeMap_comp pB
    (Subalgebra.inclusion (show T.unop.1 ≤ S.unop.1 from leOfHom g.unop))
    (Subalgebra.inclusion (show S.unop.1 ≤ R.unop.1 from leOfHom f.unop))).symm

theorem hom_spec_ext {T : Scheme.{0}} {A : CommRingCat.{0}} {f g : T ⟶ Spec A}
    (h : (Scheme.ΓSpecIso A).inv ≫ f.appTop = (Scheme.ΓSpecIso A).inv ≫ g.appTop) : f = g :=
  ext_of_isAffine ((cancel_epi _).1 h)

theorem appTop_comp_spMap {T : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (f : T ⟶ Sp A') (x : A) :
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (f ≫ spMap φ).appTop).hom x =
      ((Scheme.ΓSpecIso (.of A')).inv ≫ f.appTop).hom (φ x) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

theorem nonempty_isLimit_baseChange (h : R₀.FG) :
    Nonempty (IsLimit (schemeConeOfFamily (baseChangeDiagram R₀ pB)
      (X := pullback pB (spMap (algebraMap k C))) (fun R => baseChangeMap pB R.unop.1.val)
      (fun {R T} f => baseChangeMap_comp pB
        (Subalgebra.inclusion (show T.unop.1 ≤ R.unop.1 from leOfHom f.unop)) R.unop.1.val))) := by
  let o : FGAbove R₀ := ⟨R₀, h, le_rfl⟩
  refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
  let a : ∀ R : FGAbove R₀, s.pt ⟶ pullback pB (spMap (algebraMap k R.1)) := fun R => s.π.app (.op R)
  have ha : ∀ (R T : FGAbove R₀) (hRT : R.1 ≤ T.1),
      a T ≫ baseChangeMap pB (Subalgebra.inclusion hRT) = a R :=
    fun R T hRT => s.w (homOfLE (show R ≤ T from hRT)).op
  obtain ⟨ψ, hψ⟩ := FGAbove.exists_ringHom h
    (fun R => ((Scheme.ΓSpecIso (.of R.1)).inv ≫ (a R ≫ pullback.snd _ _).appTop).hom) (by
      intro R T hRT x
      rw [← ha R T hRT, Category.assoc, baseChangeMap_snd, ← Category.assoc (a T), appTop_comp_spMap]
      rfl)
  obtain ⟨b, hb⟩ : ∃ b : s.pt ⟶ Sp C, (Scheme.ΓSpecIso (.of C)).inv ≫ b.appTop = CommRingCat.ofHom ψ := by
    refine ⟨s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  have hb' : ∀ R : FGAbove R₀, b ≫ spMap R.1.val.toRingHom = a R ≫ pullback.snd _ _ := fun R =>
    hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => by
      rw [appTop_comp_spMap, hb]
      exact hψ R x))
  have hf : ∀ R : FGAbove R₀, a R ≫ pullback.fst _ _ = a o ≫ pullback.fst _ _ := fun R => by
    rw [← ha o R R.2.2, Category.assoc, baseChangeMap_fst]
  refine ⟨pullback.lift (a o ≫ pullback.fst _ _) b ?_, fun R => ?_, fun m hm => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ← hb' o, Category.assoc, spMap_comp_ring]
    congr 2
  · show _ ≫ baseChangeMap pB R.unop.1.val = a R.unop
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeMap_fst, pullback.lift_fst, hf R.unop]
    · rw [Category.assoc, baseChangeMap_snd, pullback.lift_snd_assoc, hb']
  · change s.pt ⟶ pullback pB (spMap (algebraMap k C)) at m
    have hm' : ∀ R : FGAbove R₀, m ≫ baseChangeMap pB R.1.val = a R := fun R => hm (.op R)
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hm' o, Category.assoc, baseChangeMap_fst]
    · rw [pullback.lift_snd]
      refine hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      obtain ⟨R, hx⟩ := FGAbove.exists_mem h x
      have e : (m ≫ pullback.snd _ _) ≫ spMap R.1.val.toRingHom = b ≫ spMap R.1.val.toRingHom := by
        rw [hb', ← hm' R, Category.assoc, Category.assoc, baseChangeMap_snd]
      exact (appTop_comp_spMap R.1.val.toRingHom _ ⟨x, hx⟩).symm.trans
        (e ▸ appTop_comp_spMap R.1.val.toRingHom b ⟨x, hx⟩)

theorem exists_fg_lbIso [QuasiCompact pB] [QuasiSeparated pB] (h : R₀.FG)
    (M N : LB (pullback pB (spMap (algebraMap k R₀)))) (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (baseChangeMap pB R₀.val)) (N.pull (baseChangeMap pB R₀.val))) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧
      LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR)))
        (N.pull (baseChangeMap pB (Subalgebra.inclusion hR))) := by
  have q₁ : QuasiCompact (pullback.snd pB (spMap (algebraMap k R₀))) :=
    quasiCompact_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have q₂ : QuasiSeparated (pullback.snd pB (spMap (algebraMap k R₀))) :=
    quasiSeparated_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have h₁ : CompactSpace ↥(pullback pB (spMap (algebraMap k R₀))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd pB (spMap (algebraMap k R₀)))
  have h₂ : QuasiSeparatedSpace ↥(pullback pB (spMap (algebraMap k R₀))) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd pB (spMap (algebraMap k R₀)))
  have := FGAbove.isFiltered h
  obtain ⟨hc⟩ := nonempty_isLimit_baseChange pB h
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom ((baseChangeDiagram R₀ pB).map f) :=
    fun _ => isAffineHom_baseChangeMap pB _
  have : CompactSpace ((baseChangeDiagram R₀ pB).obj (.op ⟨R₀, h, le_rfl⟩)) := h₁
  have : QuasiSeparatedSpace ((baseChangeDiagram R₀ pB).obj (.op ⟨R₀, h, le_rfl⟩)) := h₂
  obtain ⟨R, f, hR⟩ := exists_lbIso_of_isLimit _ _ _ hc (i := .op ⟨R₀, h, le_rfl⟩) M N hM hN H
  exact ⟨R.unop.1, R.unop.2.2, R.unop.2.1, hR⟩

end Tower

theorem lbIso_spreads_out (k : IntermediateField ℚ ℂ) (B : Scheme.{0}) (pB : B ⟶ Sp k) [QuasiCompact pB]
    [QuasiSeparated pB] (R₀ : Subalgebra k ℂ) (h : R₀.FG)
    (M N : LB (pullback pB (spMap (algebraMap k R₀)))) (hM : M.IsLB) (hN : N.IsLB)
    (j₀ : pullback pB (spMap (algebraMap k ℂ)) ⟶ pullback pB (spMap (algebraMap k R₀)))
    (h₁ : j₀ ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R₀.val.toRingHom)
    (H : LBIso (M.pull j₀) (N.pull j₀)) :
    ∃ (R : Subalgebra k ℂ) (hR : R₀ ≤ R)
      (i : pullback pB (spMap (algebraMap k R)) ⟶ pullback pB (spMap (algebraMap k R₀))), R.FG ∧
      i ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (Subalgebra.inclusion hR).toRingHom ∧
      LBIso (M.pull i) (N.pull i) := by
  obtain rfl : j₀ = baseChangeMap pB R₀.val :=
    pullback.hom_ext (h₁.trans (baseChangeMap_fst pB _).symm) (h₂.trans (baseChangeMap_snd pB _).symm)
  obtain ⟨R, hR, hfg, hiso⟩ := exists_fg_lbIso pB h M N hM hN H
  exact ⟨R, hR, _, hfg, baseChangeMap_fst pB _, baseChangeMap_snd pB _, hiso⟩

end GlobalTheory

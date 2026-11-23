import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenLimit

theorem exists_gen_of_subcover {Y : Scheme.{0}} {N : LB Y} (hN : N.IsLB) {J : Type} (W : J → Y.Opens)
    (hW : ∀ y, ∃ k, y ∈ W k) (a : J → N.ι) (ha : ∀ k, W k ≤ N.U (a k)) (u : ∀ k, Γ(Y, W k)ˣ)
    (hu : ∀ k l y, y ∈ W k → y ∈ W l →
      gm (𝟙 Y) y _ (u k) = gm (𝟙 Y) y _ (N.g (a k) (a l)) * gm (𝟙 Y) y _ (u l)) :
    ∃ t : LB.Gen N, t.IsGen := by
  have glue : ∀ i : N.ι, ∃ s : Γ(Y, N.U i)ˣ, ∀ k y, y ∈ N.U i → y ∈ W k →
      gm (𝟙 Y) y _ s = gm (𝟙 Y) y _ (N.g i (a k)) * gm (𝟙 Y) y _ (u k) := by
    intro i
    let v : ∀ k, Γ(Y, N.U i ⊓ W k)ˣ := fun k =>
      res (inf_le_inf_left _ (ha k)) (N.g i (a k)) * res inf_le_right (u k)
    have hv : ∀ k y, y ∈ N.U i ⊓ W k →
        gm (𝟙 Y) y _ (v k) = gm (𝟙 Y) y _ (N.g i (a k)) * gm (𝟙 Y) y _ (u k) := fun k y hy =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))
    obtain ⟨s, hs⟩ := glue_unit (N.U i) (fun k => N.U i ⊓ W k) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨k, hk⟩ := hW y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) v (fun k l y hy => by
        rw [hv k y hy.1, hv l y hy.2, hu k l y hy.1.2 hy.2.2, ← _root_.mul_assoc,
          gm_cocycle hN (𝟙 Y) y hy.1.1 (ha k hy.1.2) (ha l hy.2.2)])
    refine ⟨s, fun k y hi hk => ?_⟩
    rw [← hv k y ⟨hi, hk⟩, ← hs k]
    exact (gm_res _ y _ (show y ∈ N.U i ⊓ W k from ⟨hi, hk⟩) _).symm
  choose s hs using glue
  refine ⟨⟨s⟩, fun i j => unit_ext fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hW y
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y _ hy _))).symm)
  show gm (𝟙 Y) y _ (s i) = _ * gm (𝟙 Y) y _ (s j)
  rw [hs i k y hy.1 hk, hs j k y hy.2 hk, ← _root_.mul_assoc,
    gm_cocycle hN (𝟙 Y) y hy.1 hy.2 (ha k hk)]

theorem exists_forall_of_cofiltered {I : Type} [Category.{0} I] [IsCofiltered I] {i : I} {J : Type}
    [Finite J] (P : J → ∀ j : I, (j ⟶ i) → Prop)
    (mono : ∀ k j j' (g : j' ⟶ j) (f : j ⟶ i), P k j f → P k j' (g ≫ f))
    (ex : ∀ k, ∃ j f, P k j f) : ∃ j f, ∀ k, P k j f := by
  classical
  have := Fintype.ofFinite J
  choose j f hf using ex
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists (C := Over i)
    (Finset.univ.image fun k => Over.mk (f k))
  refine ⟨S.left, S.hom, fun k => ?_⟩
  obtain ⟨g⟩ := hS (X := Over.mk (f k)) (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have := mono k _ _ g.left (f k) (hf k)
  rwa [show g.left ≫ f k = S.hom from Over.w g] at this

section Limit

variable {I : Type} [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

theorem gm_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens)
    (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  apply Units.ext
  rw [gm_val (r ≫ q) z U h]
  show _ = (r.stalkMap z).hom (gm q (r z) U a).val
  rw [gm_val q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ U) z h _).symm

theorem gm_mul_comp {X X' Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (q' : Y ⟶ X') (z : Z)
    {U V : X.Opens} {W : X'.Opens} (hU : q (r z) ∈ U) (hV : q (r z) ∈ V) (hW : q' (r z) ∈ W)
    {a : Γ(X, U)ˣ} {b : Γ(X', W)ˣ} {d : Γ(X, V)ˣ}
    (h : gm q (r z) U a = gm q' (r z) W b * gm q (r z) V d) :
    gm (r ≫ q) z U a = gm (r ≫ q') z W b * gm (r ≫ q) z V d := by
  rw [gm_comp r q z U hU, gm_comp r q z V hV, gm_comp r q' z W hW, h, map_mul]

include hc in

theorem exists_section [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i))) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U))
      (e : c.π.app i ⁻¹ᵁ U ≤ c.π.app j ⁻¹ᵁ (D.map f ⁻¹ᵁ U)), (c.π.app j).appLE _ _ e t = s := by
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.1 ((D.map j.hom).isCompact_preimage hU)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    QuasiSeparatedSpace.of_isOpenEmbedding (D.map j.hom ⁻¹ᵁ U).ι.isOpenEmbedding
  obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isLimit _ _ (isLimitOpensCone D c hc i U)
    ((c.π.app i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t,
    (by rw [← Scheme.Hom.comp_preimage, c.w]), ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (c.π.app i ⁻¹ᵁ U).topIso.inv).1
  rw [ht]
  exact (congrArg (fun q => q.hom t) (Scheme.Hom.resLE_app_top (c.π.app j.left)
    (show c.π.app i ⁻¹ᵁ U ≤ c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ U) by
      rw [← Scheme.Hom.comp_preimage, c.w]))).symm

include hc in

theorem exists_unit [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i))) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ U)ˣ) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ),
      ∀ z, c.π.app i z ∈ U → gm (c.π.app j) z _ t = gm (𝟙 c.pt) z _ s := by
  obtain ⟨j, f, t, e, ht⟩ := exists_section D c hc U hU s.val
  have e' : c.π.app j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) = c.π.app i ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  have h1 : c.π.app j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) ≤ c.π.app j ⁻¹ᵁ (D.obj j).basicOpen t := by
    have := Scheme.basicOpen_appLE (c.π.app j) _ _ e t
    rw [ht] at this
    exact e'.le.trans (((c.pt.basicOpen_of_isUnit s.isUnit).symm.trans this).le.trans inf_le_right)
  obtain ⟨k, g, hg⟩ := exists_map_preimage_le_map_preimage D c hc
    ((D.map f).isCompact_preimage hU) h1
  have e₂ : D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := by
    rw [D.map_comp]; exact le_rfl
  have hu : IsUnit ((D.map g).appLE _ _ e₂ t) := by
    refine RingedSpace.isUnit_of_isUnit_germ (D.obj k).toRingedSpace _ _ fun x hx => ?_
    refine ((D.obj k).mem_basicOpen _ x hx).1 ?_
    rw [Scheme.basicOpen_appLE]
    exact ⟨hx, hg (e₂ hx)⟩
  refine ⟨k, g ≫ f, hu.unit, fun z hz => ?_⟩
  have e₃ : c.π.app i ⁻¹ᵁ U ≤ c.π.app k ⁻¹ᵁ (D.map (g ≫ f) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  rw [← gm_rp₁ (c.π.app k) z _ _ e₃ hz]
  congr 1
  apply Units.ext
  rw [← ht]
  show ((D.map g).appLE _ _ e₂ ≫ (c.π.app k).appLE _ _ e₃) t = _
  rw [Scheme.Hom.appLE_comp_appLE]
  have w : c.π.app k ≫ D.map g = c.π.app j := c.w g
  congr 2
  simp only [w]

include hc in

theorem exists_unit_eq {i : I} (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i))) (s t : Γ(D.obj i, U)ˣ)
    (h : ∀ z, c.π.app i z ∈ U → gm (c.π.app i) z _ s = gm (c.π.app i) z _ t) :
    ∃ (j : I) (f : j ⟶ i), ∀ y, D.map f y ∈ U → gm (D.map f) y _ s = gm (D.map f) y _ t := by
  have h1 : pullU (c.π.app i) U s = pullU (c.π.app i) U t := unit_ext fun z hz => by
    rw [gm_id_pull _ _ _ hz, gm_id_pull _ _ _ hz, h z hz]
  obtain ⟨j, f, hf⟩ := exists_app_map_eq_map_of_isLimit D c hc hU s.val t.val
    (congrArg Units.val h1)
  refine ⟨j, f, fun y hy => ?_⟩
  apply Units.ext
  rw [gm_val _ _ _ hy, gm_val _ _ _ hy]
  exact congrArg _ hf

theorem exists_generator_stage_of_unit_descent [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {P : Scheme.{0}} (ρ : ∀ j, P ⟶ D.obj j) (hw : ∀ {j i : I} (f : j ⟶ i), ρ j ≫ D.map f = ρ i)
    (H₁ : ∀ {i : I} (U : (D.obj i).Opens) (_ : IsCompact (U : Set (D.obj i))) (s : Γ(P, ρ i ⁻¹ᵁ U)ˣ),
      ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ),
        ∀ z, ρ i z ∈ U → gm (ρ j) z _ t = gm (𝟙 P) z _ s)
    (H₂ : ∀ {i : I} (U : (D.obj i).Opens) (_ : IsCompact (U : Set (D.obj i))) (s t : Γ(D.obj i, U)ˣ),
      (∀ z, ρ i z ∈ U → gm (ρ i) z _ s = gm (ρ i) z _ t) →
      ∃ (j : I) (f : j ⟶ i), ∀ y, D.map f y ∈ U → gm (D.map f) y _ s = gm (D.map f) y _ t)
    {i : I} {M : LB (D.obj i)} (hM : M.IsLB) (h : ∃ t : LB.Gen (M.pull (ρ i)), t.IsGen) :
    ∃ (j : I) (f : j ⟶ i) (t : LB.Gen (M.pull (D.map f))), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  have loc : ∀ x : D.obj i, ∃ (a : M.ι) (W : (D.obj i).Opens),
      IsCompact (W : Set (D.obj i)) ∧ x ∈ W ∧ W ≤ M.U a := fun x => by
    obtain ⟨a, ha⟩ := exists_chart hM x
    obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hx, hle⟩ :=
      (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open ha (M.U a).isOpen
    exact ⟨a, W, hW.isCompact, hx, hle⟩
  choose a₀ W₀ hc₀ hx₀ hle₀ using loc
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (W₀ x : Set (D.obj i)))
    (fun x => (W₀ x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx₀ x⟩)
  let W : S → (D.obj i).Opens := fun k => W₀ k
  let a : S → M.ι := fun k => a₀ k
  have hW : ∀ y, ∃ k, y ∈ W k := fun y => by
    obtain ⟨k, hk, hy⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ y))
    exact ⟨⟨k, hk⟩, hy⟩
  have hle : ∀ k, W k ≤ M.U (a k) := fun k => hle₀ k
  have hle' : ∀ {Y : Scheme.{0}} (q : Y ⟶ D.obj i) k, q ⁻¹ᵁ W k ≤ (M.pull q).U (fun _ => a k) :=
    fun q k y hy => mem_pull.2 (hle k hy)
  let u : ∀ k, Γ(P, ρ i ⁻¹ᵁ W k)ˣ := fun k => res (hle' _ k) (t.s fun _ => a k)
  have hu : ∀ k l z, ρ i z ∈ W k → ρ i z ∈ W l →
      gm (𝟙 P) z _ (u k) = gm (ρ i) z _ (M.g (a k) (a l)) * gm (𝟙 P) z _ (u l) := by
    intro k l z hk hl
    have hm : z ∈ (M.pull (ρ i)).U (fun _ => a k) ⊓ (M.pull (ρ i)).U (fun _ => a l) :=
      ⟨hle' _ k hk, hle' _ l hl⟩
    have e := (gm_res (𝟙 P) z _ hm _).symm.trans ((congrArg (gm (𝟙 P) z _)
      (ht (fun _ => a k) (fun _ => a l))).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (gm_pull_g M _ (𝟙 P) z _ _ hm.1 hm.2) (gm_res (𝟙 P) z _ hm _))))
    rw [Category.id_comp] at e
    exact (gm_res (𝟙 P) z (hle' (ρ i) k) hk _).trans (e.trans
      (congrArg₂ (· * ·) rfl (gm_res (𝟙 P) z (hle' (ρ i) l) hl _).symm))
  have hmap : ∀ {j j' : I} (g : j' ⟶ j) (f : j ⟶ i) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun g f U => by
    rw [D.map_comp]; exact le_rfl
  have hπ : ∀ {j : I} (f : j ⟶ i) (z : P), D.map f (ρ j z) = ρ i z := fun f z =>
    congrArg (fun q => q z) (hw f)
  have hcW : ∀ k, IsCompact (W k : Set (D.obj i)) := fun k => hc₀ k
  clear_value u W a
  let Q : S → ∀ j, (j ⟶ i) → Prop := fun k j f => ∃ v : Γ(D.obj j, D.map f ⁻¹ᵁ W k)ˣ,
      ∀ z, ρ i z ∈ W k → gm (ρ j) z _ v = gm (𝟙 P) z _ (u k)
  have Qmono : ∀ k j j' (g : j' ⟶ j) (f : j ⟶ i), Q k j f → Q k j' (g ≫ f) := by
    rintro k j j' g f ⟨v, hv⟩
    refine ⟨res (hmap g f _) (pullU (D.map g) _ v), fun z hz => ?_⟩
    have m : ρ j' z ∈ D.map (g ≫ f) ⁻¹ᵁ W k := by
      show D.map (g ≫ f) (ρ j' z) ∈ W k
      rw [hπ]; exact hz
    refine (gm_res _ _ _ m _).trans
      ((gm_pull (ρ j') (D.map g) z (D.map f ⁻¹ᵁ W k) (hmap g f _ m) v).trans ?_)
    rw [hw g]
    exact hv z hz
  obtain ⟨j, f, hv⟩ := exists_forall_of_cofiltered Q Qmono (fun k => H₁ (W k) (hcW k) (u k))
  choose v hv using hv
  let Q' : S × S → ∀ n, (n ⟶ j) → Prop := fun p n g =>
    ∀ y, D.map g y ∈ D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2) →
      gm (D.map g) y _ (v p.1) =
        gm (D.map g ≫ D.map f) y _ (M.g (a p.1) (a p.2)) * gm (D.map g) y _ (v p.2)
  have Q'mono : ∀ p n n' (g' : n' ⟶ n) (g : n ⟶ j), Q' p n g → Q' p n' (g' ≫ g) := by
    intro p n n' g' g H y hy
    have hy' : D.map g (D.map g' y) ∈ D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2) := by
      rw [D.map_comp] at hy; exact hy
    rw [D.map_comp, Category.assoc]
    exact gm_mul_comp (D.map g') (D.map g) (D.map g ≫ D.map f) y
      (U := D.map f ⁻¹ᵁ W p.1) (V := D.map f ⁻¹ᵁ W p.2) (W := M.U (a p.1) ⊓ M.U (a p.2)) hy'.1 hy'.2
      ⟨hle _ hy'.1, hle _ hy'.2⟩ (H (D.map g' y) hy')
  have Q'ex : ∀ p, ∃ n g, Q' p n g := by
    intro p
    have l₁ : D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2) ≤ D.map f ⁻¹ᵁ W p.1 := fun _ h => h.1
    have l₂ : D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2) ≤ D.map f ⁻¹ᵁ W p.2 := fun _ h => h.2
    have l₃ : D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2) ≤ D.map f ⁻¹ᵁ (M.U (a p.1) ⊓ M.U (a p.2)) :=
      fun _ h => ⟨hle _ h.1, hle _ h.2⟩
    have key : ∀ {Y : Scheme.{0}} (q : Y ⟶ D.obj j) (y : Y), q y ∈ D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2) →
        gm q y _ (res l₃ (pullU (D.map f) _ (M.g (a p.1) (a p.2))) * res l₂ (v p.2)) =
          gm (q ≫ D.map f) y _ (M.g (a p.1) (a p.2)) * gm q y _ (v p.2) := fun q y hy =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res q y l₃ hy _).trans
        (gm_pull q (D.map f) y (M.U (a p.1) ⊓ M.U (a p.2)) (l₃ hy) _)) (gm_res q y l₂ hy _))
    have hcp : IsCompact ((W p.1 ⊓ W p.2 : (D.obj i).Opens) : Set (D.obj i)) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hcW p.1) (W p.2).isOpen (hcW p.2)
    obtain ⟨n, g, H⟩ := H₂ (D.map f ⁻¹ᵁ (W p.1 ⊓ W p.2)) ((D.map f).isCompact_preimage hcp)
      (res l₁ (v p.1)) (res l₃ (pullU (D.map f) _ (M.g (a p.1) (a p.2))) * res l₂ (v p.2))
      (fun z hz => by
        have m : ρ i z ∈ W p.1 ⊓ W p.2 := by
          rw [← hπ f z]; exact hz
        refine (gm_res (ρ j) z l₁ hz _).trans (Eq.trans ?_ (key (ρ j) z hz).symm)
        rw [hw f, hv _ z m.1, hv _ z m.2]
        exact hu _ _ z m.1 m.2)
    exact ⟨n, g, fun y hy =>
      (gm_res (D.map g) y l₁ hy _).symm.trans ((H y hy).trans (key (D.map g) y hy))⟩
  obtain ⟨n, g, hg⟩ := exists_forall_of_cofiltered Q' Q'mono Q'ex
  refine ⟨n, g ≫ f, exists_gen_of_subcover (pull_isLB hM _) (fun k => D.map (g ≫ f) ⁻¹ᵁ W k)
    (fun y => hW (D.map (g ≫ f) y)) (fun k _ => a k) (hle' (D.map (g ≫ f)))
    (fun k => res (hmap g f _) (pullU (D.map g) _ (v k))) fun k l y hk hl => ?_⟩
  refine (gm_rp₁ _ y _ _ _ hk _).trans ((hg (k, l) y ⟨hmap g f _ hk, hmap g f _ hl⟩).trans
    (congrArg₂ (· * ·) ?_ (gm_rp₁ _ y _ _ _ hl _).symm))
  refine Eq.trans ?_ (gm_pull_g M _ (𝟙 _) y _ _ (hle' _ k hk) (hle' _ l hl)).symm
  rw [Category.id_comp, D.map_comp]

include hc in

theorem exists_gen_stage [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
    {M : LB (D.obj i)} (hM : M.IsLB) (h : ∃ t : LB.Gen (M.pull (c.π.app i)), t.IsGen) :
    ∃ (j : I) (f : j ⟶ i) (t : LB.Gen (M.pull (D.map f))), t.IsGen :=
  exists_generator_stage_of_unit_descent D (P := c.pt) (fun j => c.π.app j) (fun f => c.w f)
    (fun U hU s => exists_unit D c hc U hU s) (fun U hU s t h => exists_unit_eq D c hc U hU s t h) hM h

end Limit

section Base

variable {S : Scheme.{0}} (A : Over S)

theorem isPullback_whiskerRight {T T' : Over S} (a : T' ⟶ T) :
    IsPullback (a ▷ A).left (fst T' A).left (fst T A).left a.left := by
  have h : ∀ T : Over S, IsPullback (snd T A).left (fst T A).left A.hom T.hom := fun T =>
    (IsPullback.of_hasPullback T.hom A.hom).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (whiskerRight_fst a A)) (h T)
  rw [Over.w a, show (a ▷ A).left ≫ (snd T A).left = (snd T' A).left from
    congrArg (fun q => q.left) (whiskerRight_snd a A)]
  exact h T'

theorem compactSpace_tensor [QuasiCompact A.hom] (T : Over S) (_ : IsAffine T.left) :
    CompactSpace (T ⊗ A).left :=
  have : QuasiCompact (fst T A).left :=
    inferInstanceAs (QuasiCompact (pullback.fst T.hom A.hom))
  QuasiCompact.compactSpace_of_compactSpace (fst T A).left

theorem quasiSeparatedSpace_tensor [QuasiSeparated A.hom] (T : Over S) (_ : IsAffine T.left) :
    QuasiSeparatedSpace (T ⊗ A).left :=
  have : QuasiSeparated (fst T A).left :=
    inferInstanceAs (QuasiSeparated (pullback.fst T.hom A.hom))
  (quasiSeparated_iff_quasiSeparatedSpace (fst T A).left).mp this

variable [GrpObj A] (L : LB A.left)

theorem whiskerRight_transl {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ A) (k : Fin 2) :
    ![(lift (fst T' A ≫ a ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] k =
      (a ▷ A).left ≫ ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k := by
  fin_cases k
  · refine congrArg (fun q => q.left) (show lift (fst T' A ≫ a ≫ x) (snd T' A) ≫ μ[A] =
      (a ▷ A) ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A] from ?_)
    rw [← Category.assoc (a ▷ A), comp_lift, whiskerRight_fst_assoc, whiskerRight_snd]
  · exact congrArg (fun q => q.left) (whiskerRight_snd a A).symm

theorem gen_pull_of_gen {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ A)
    (h : ∃ c : LB.Gen (Out.translDiff A L (a ≫ x)), c.IsGen) :
    ∃ c : LB.Gen ((Out.translDiff A L x).pull (a ▷ A).left), c.IsGen := by
  obtain ⟨c, hc⟩ := h
  exact gen_chartPull (chartPullOut L _ _ _ _ (whiskerRight_transl A a x)) c hc

theorem gen_of_gen_pull {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ A)
    (h : ∃ c : LB.Gen ((Out.translDiff A L x).pull (a ▷ A).left), c.IsGen) :
    ∃ c : LB.Gen (Out.translDiff A L (a ≫ x)), c.IsGen := by
  obtain ⟨c, hc⟩ := h
  have := gen_chartPull (chartPullIn L _ _ _) c hc
  rw [← funext (whiskerRight_transl A a x)] at this
  exact this

end Base

end GlobalTheory.GenLimit

namespace GlobalTheory

open GenLimit

theorem translDiff_gen_eq_one_of_finiteType : (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) := by
  intro A _ L hA hL H R _ _ x hx
  classical
  have := hA.proper
  have := hA.smooth
  let F : Finset R ⥤ CommRingCat.{0} :=
    { obj s := .of (Algebra.adjoin ℂ (s : Set R))
      map {s t} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cF : Cocone F :=
    { pt := .of R
      «ι» := { app s := CommRingCat.ofHom (Algebra.adjoin ℂ (s : Set R)).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcF : IsColimit cF := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : R := x
        exact ⟨({x'} : Finset R), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin ℂ (({x'} : Finset R) : Set R)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset R)ᵒᵖ ⥤ Scheme.{0} := F.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cF.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcF.op
  let κ (s : (Finset R)ᵒᵖ) : G.obj s ⟶ Sp ℂ :=
    spMap (algebraMap ℂ (Algebra.adjoin ℂ (s.unop : Set R)))
  have hι {s t : (Finset R)ᵒᵖ} (f : s ⟶ t) : G.map f ≫ κ t = κ s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (s : (Finset R)ᵒᵖ) : cG.π.app s ≫ κ s = spMap (algebraMap ℂ R) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let T₀ : Over (Sp ℂ) := Over.mk (spMap (algebraMap ℂ R))
  let T : (Finset R)ᵒᵖ ⥤ Over (Sp ℂ) :=
    { obj s := Over.mk (κ s)
      map f := Over.homMk (G.map f) (hι f)
      map_id s := Over.OverMorphism.ext (G.map_id s)
      map_comp f g := Over.OverMorphism.ext (G.map_comp f g) }
  let p (s : (Finset R)ᵒᵖ) : T₀ ⟶ T.obj s := Over.homMk (cG.π.app s) (hι' s)
  have hp {s t : (Finset R)ᵒᵖ} (f : s ⟶ t) : p s ≫ T.map f = p t :=
    Over.OverMorphism.ext (cG.w f)
  let D : (Finset R)ᵒᵖ ⥤ Scheme.{0} := T ⋙ tensorRight A ⋙ Over.forget _
  let α : D ⟶ G :=
    { app s := (fst (T.obj s) A).left
      naturality s t f := (isPullback_whiskerRight A (T.map f)).w }
  let cD : Cone D :=
    { pt := (T₀ ⊗ A).left
      π :=
        { app s := (p s ▷ A).left
          naturality s t f := (Category.id_comp _).trans (congrArg (fun q => q.left)
            (show p t ▷ A = p s ▷ A ≫ T.map f ▷ A by rw [← comp_whiskerRight, hp])) } }
  have hcD : IsLimit cD := isLimitOfIsPullbackOfIsConnected α cD cG
    { hom := (fst T₀ A).left, w s := (isPullback_whiskerRight A (p s)).w.symm }
    (fun s => isPullback_whiskerRight A (p s)) hcG
  have hG (s : (Finset R)ᵒᵖ) : IsAffine (G.obj s) := inferInstanceAs (IsAffine (Spec _))
  have hGa {s t : (Finset R)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (G.map f) := inferInstance
  have {s t : (Finset R)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f) :=
    MorphismProperty.of_isPullback (isPullback_whiskerRight A (T.map f)).flip (hGa f)
  have (s : (Finset R)ᵒᵖ) : CompactSpace (D.obj s) := compactSpace_tensor A (T.obj s) (hG s)
  have (s : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj s) :=
    quasiSeparatedSpace_tensor A (T.obj s) (hG s)
  obtain ⟨i, y₀, hy₀, hy₁⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation G
    ({ app := κ, naturality := fun s t f => (hι f).trans (Category.comp_id _).symm } :
      G ⟶ (Functor.const _).obj (Sp ℂ)) A.hom cG hcG x.left
    (NatTrans.ext (funext fun s => (hι' s).trans (Over.w x).symm))
  let y : T.obj i ⟶ A := Over.homMk y₀ hy₁
  have hy : p i ≫ y = x := Over.OverMorphism.ext hy₀
  obtain ⟨j, f, hf⟩ := exists_gen_stage D cD hcD (i := i) (M := Out.translDiff A L y)
    (DVR.linComb_isLB L hL _ _) (gen_pull_of_gen A L (p i) y (hy.symm ▸ hx))
  have e := H (Algebra.adjoin ℂ (j.unop : Set R))
    (Algebra.FiniteType.adjoin_of_finite j.unop.finite_toSet) (T.map f ≫ y)
    (gen_of_gen_pull A L (T.map f) y hf)
  have e' : p j ≫ T.map f ≫ y = p j ≫ 1 := congrArg (p j ≫ ·) e
  rw [← Category.assoc, hp, hy, MonObj.comp_one] at e'
  exact e'

end GlobalTheory

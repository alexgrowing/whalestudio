import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace NumberField
  IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

def AmplePtSt : Prop :=
  ∀ (S : Scheme.{0}) (K : Type) [Field K] (f : Sp K ⟶ S) (A : Over S) (A' : Over (Sp K)) [GrpObj A] [GrpObj A']
    (φ : A'.left ⟶ A.left), IsGrpPullback A' A f φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
    LBIso L' (L.pull φ) → RelAmple A L → KTriv A L → RelAmple A' L' ∧ KTriv A' L'

theorem exists_dim_of_preconnected {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] (x₀ : X) :
    ∃ n, SmoothOfRelativeDimension n f := by
  choose n W hW hd using exists_dim f
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ f) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ f) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n := (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀)) W
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_⟩
  rw [hc.apply_eq_of_preconnectedSpace x₀ x]; exact hd x

section Down

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem sec_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (σ : ∀ j, Γ(X', F ⁻¹ᵁ L.U j))
    (hσ : ∀ (y : X') j j', F y ∈ L.U j → F y ∈ L.U j' →
      gs (𝟙 X') y _ (σ j) = (gm F y (L.U j ⊓ L.U j') (L.g j j')).val * gs (𝟙 X') y _ (σ j')) :
    ∃ s : LB.Sec L', ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (σ j) = (gw w r z j k).val * gs r z _ (s.f k) := by
  have le : ∀ j k, L'.U k ⊓ F ⁻¹ᵁ L.U j ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k := fun j k y hy => ⟨mem_pull.2 hy.2, hy.1⟩
  have tr : ∀ (y : X') j j' k k', F y ∈ L.U j → F y ∈ L.U j' → y ∈ L'.U k → y ∈ L'.U k' → gw w (𝟙 X') y j k =
      gm F y _ (L.g j j') * (gm (𝟙 X') y _ (L'.g k k'))⁻¹ * gw w (𝟙 X') y j' k' := fun y j j' k k' a b c d => by
    have := hw _ (𝟙 X') y j j' k k' a b c d
    rwa [Category.id_comp] at this
  have glue : ∀ k, ∃ a : Γ(X', L'.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ a = ((gw w r z j k)⁻¹).val * gs r z _ (σ j) := by
    intro k
    obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(X', L'.U k ⊓ F ⁻¹ᵁ L.U j), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j,
        r z ∈ L'.U k ⊓ F ⁻¹ᵁ L.U j → gs r z _ (u j) = ((gw w r z j k)⁻¹).val * gs r z _ (σ j) :=
      ⟨fun j => ((res (le j k) (w.s (fun _ => j, k)))⁻¹).val * resG X' inf_le_right (σ j), fun Z r z j hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le j k) hz _))))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' (fun j => L'.U k ⊓ F ⁻¹ᵁ L.U j) (L'.U k)
      (fun j => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hL (F y)
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩) u
      (fun j j' => fn_ext (V := (L'.U k ⊓ F ⁻¹ᵁ L.U j) ⊓ (L'.U k ⊓ F ⁻¹ᵁ L.U j')) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu _ _ y j hy.1, hu _ _ y j' hy.2, hσ y j j' hy.1.2 hy.2.2, tr y j j' k k hy.1.2 hy.2.2 hy.1.1 hy.1.1,
          gm_self hL' (𝟙 X') y hy.1.1, inv_one, _root_.mul_one, ← _root_.mul_assoc, ← Units.val_mul, mul_inv,
          mul_right_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨a, fun Z r z j h₁ h₂ => ?_⟩
    have hz : r z ∈ L'.U k ⊓ F ⁻¹ᵁ L.U j := ⟨h₂, h₁⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha j)).trans (hu Z r z j hz))
  choose a ha using glue
  refine ⟨⟨a, fun k k' => fn_ext fun y hy => ?_⟩, fun Z r z j k h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (F y)
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, ha k _ _ y j hj hy.1, ha k' _ _ y j hj hy.2,
      tr y j j k k' hj hj hy.1 hy.2, gm_self hL F y hj, _root_.one_mul, mul_inv, inv_inv, Units.val_mul, _root_.mul_assoc]
  · show _ = _ * gs r z _ (a k)
    rw [ha k Z r z j h₁ h₂, Units.mul_inv_cancel_left]

theorem gs_compat (s : LB.Sec L) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {j j' : L.ι} (h : r z ∈ L.U j) (h' : r z ∈ L.U j') :
    gs r z _ (s.f j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z _ (s.f j') := by
  have hjj : r z ∈ L.U j ⊓ L.U j' := ⟨h, h'⟩
  have R : ∀ {W W' : X.Opens} (hle : W' ≤ W) (f : Γ(X, W)) (hw : r z ∈ W'),
      gs r z W f = gs r z W' ((X.presheaf.map (homOfLE hle).op).hom f) := by
    intro W W' hle f hw
    unfold gs
    rw [dif_pos (show r z ∈ W from hle hw), dif_pos hw]
    have n1 := congrArg (fun φ => CommRingCat.Hom.hom φ f) (r.naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Quiver.Hom.unop_op] at n1
    rw [n1]
    have g1 := congrArg (fun φ => CommRingCat.Hom.hom φ ((r.app W).hom f))
      (Z.presheaf.germ_res ((TopologicalSpace.Opens.map r.base).map (homOfLE hle)) z hw)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at g1
    rw [g1]
  rw [R (inf_le_left : L.U j ⊓ L.U j' ≤ L.U j) (s.f j) hjj,
    R (inf_le_right : L.U j ⊓ L.U j' ≤ L.U j') (s.f j') hjj, s.2 j j']
  unfold gs
  simp only [dif_pos hjj]
  rw [map_mul, map_mul]
  congr 1
  first
  | rfl
  | (unfold gm; rfl)
  | (unfold gm; simp only [dif_pos hjj]; rfl)
  | (unfold gm; simp only [dif_pos hjj, Units.coe_map, MonoidHom.coe_coe]; rfl)
  | (unfold gm; simp [hjj]; done)

theorem sec_pull_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  have p : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.app _).hom (s.f j)) = gs F y _ (s.f j) := fun y j h =>
    (gs_pull (𝟙 X') F y _ h _).trans (by rw [Category.id_comp])
  obtain ⟨s', hs'⟩ := sec_down hw hL hL' (fun j => (F.app _).hom (s.f j)) fun y j j' h h' =>
    (p y j h).trans ((gs_compat s F y h h').trans (congrArg _ (p y j' h').symm))
  exact ⟨s', fun Z r z j k h₁ h₂ => (gs_pull r F z _ h₁ _).symm.trans (hs' Z r z j k h₁ h₂)⟩

theorem exists_iso_linComb (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (X' ⟶ X)) (ε : K → ℤ)
    (h : FormEq φ ε (fun _ : PUnit => F) (fun _ => 1)) : LBIso (LB.LinComb L φ ε) (L.pull F) := by
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := Sum.elim (fun _ : PUnit => F) φ) (ε' := Sum.elim (fun _ => 1) (fun k => -ε k))
    (fun U _ k => (Fintype.prod_empty _).trans (Eq.symm ((prod_sum₂ (K := PUnit) (K' := K) (U := U) _ (h U k).symm
      (prod_neg _ _ rfl)).trans (mul_inv_cancel _)))) (LB.oneGen L (Y := X'))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have le : ∀ p : (PUnit → L.ι) × (K → L.ι), LB.wchart L (fun _ : PUnit => F) p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim (fun _ : PUnit => F) φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  refine ⟨⟨fun p => res (le p) (t.s (Sum.elim p.1 p.2))⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (gen_trans ht (𝟙 X') y (le p hy.1) (le q hy.2)))).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div _ _ (𝟙 X') y p q hy).trans ?_)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))))
  exact (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L _ _ (𝟙 X') y p.1 q.1 hy.1.1 hy.2.1)
    (gm_linComb L φ ε (𝟙 X') y p.2 q.2 hy.1.2 hy.2.2)).trans
    (Eq.symm ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_neg _ ε rfl))))

def chartPullSec (L : LB X) (F : X' ⟶ X) (ρ : X ⟶ X') (e : ρ ≫ F = 𝟙 X) : ChartPull L (L.pull F) ρ :=
  have m : ∀ i (y : X), y ∈ L.U i → ρ y ∈ (L.pull F).U (fun _ => i) := fun i y h =>
    mem_pull.2 ((congrArg (fun q => q y ∈ L.U i) e).mpr h)
  { idx := fun i _ => i
    le := m
    g := fun y i j hi hj => ((gm_pull_g L F ρ y _ _ (m i y hi) (m j y hj)).trans (by rw [e])).symm }

theorem cst_sub {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) (a b : V) :
    cst q z (a - b) = cst q z a - cst q z b := by
  unfold cst gs
  split_ifs
  · simp only [map_sub]
  · simp only [sub_self]

theorem sec_eq_iff {V : Type} [CommRing V] (p : X ⟶ Sp V) (s t : LB.Sec L) (a : V) :
    (∀ i, s.f i = constFn p _ a * t.f i) ↔
      ∀ i, ∀ y ∈ L.U i, gs (𝟙 X) y _ (s.f i) = cst p y a * gs (𝟙 X) y _ (t.f i) := by
  have G1 : ∀ (W : X.Opens) (y : X) (hy : y ∈ W) (f : Γ(X, W)),
      gs (𝟙 X) y W f = (X.presheaf.germ W y hy).hom f := by
    intro W y hy f
    unfold gs
    rw [dif_pos (show (𝟙 X : X ⟶ X) y ∈ W from hy)]
    first
    | rfl
    | (simp only [Scheme.id_app, CommRingCat.hom_id, RingHom.id_apply]; rfl)
  have G2 : ∀ i (y : X) (hy : y ∈ L.U i),
      cst p y a = (X.presheaf.germ (L.U i) y hy).hom (constFn p (L.U i) a) := by
    intro i y hy
    unfold cst gs constFn
    rw [dif_pos (by trivial)]
    unfold Scheme.Hom.appLE
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    have e := congrArg (fun φ => CommRingCat.Hom.hom φ ((CommRingCat.Hom.hom (p.app ⊤))
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of V)).inv) a)))
      (X.presheaf.germ_res (homOfLE (show L.U i ≤ p ⁻¹ᵁ ⊤ from le_top)) y hy)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [e]
  constructor
  · intro h i y hy
    rw [G1 _ y hy, G1 _ y hy, G2 i y hy, h i, map_mul]
  · intro h i
    apply TopCat.Presheaf.section_ext X.sheaf
    intro y hy
    have e := h i y hy
    rw [G1 _ y hy, G1 _ y hy, G2 i y hy, ← map_mul] at e
    exact e

theorem gs_of_id {Z : Scheme.{0}} {U : X.Opens} {f g : Γ(X, U)} {V : Type} [CommRing V] {p : X ⟶ Sp V} {a : V}
    (r : Z ⟶ X) (z : Z) (hz : r z ∈ U) (h : gs (𝟙 X) (r z) U f = cst p (r z) a * gs (𝟙 X) (r z) U g) :
    gs r z U f = cst (r ≫ p) z a * gs r z U g := by
  have B : ∀ {Y : Scheme.{0}} (p' : X ⟶ Y) (W : Y.Opens) (t : Γ(Y, W)) (hw : p' (r z) ∈ W),
      gs (r ≫ p') z W t = (r.stalkMap z).hom (gs p' (r z) W t) := by
    intro Y p' W t hw
    unfold gs
    rw [dif_pos (show (r ≫ p') z ∈ W from hw), dif_pos hw]
    have e := congrArg (fun φ => CommRingCat.Hom.hom φ ((CommRingCat.Hom.hom (p'.app W)) t))
      (Scheme.Hom.germ_stalkMap r (p' ⁻¹ᵁ W) z hw)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [e]
    first
    | rfl
    | (simp only [Scheme.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; rfl)
    | (simp only [Scheme.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; done)
  have A : ∀ (W : X.Opens) (t : Γ(X, W)) (hw : r z ∈ W),
      gs r z W t = (r.stalkMap z).hom (gs (𝟙 X) (r z) W t) := by
    intro W t hw
    have e := B (𝟙 X) W t hw
    rwa [Category.comp_id] at e
  have C : cst (r ≫ p) z a = (r.stalkMap z).hom (cst p (r z) a) := by
    unfold cst
    exact B p ⊤ _ trivial
  rw [A U f hz, A U g hz, C, h, map_mul]

theorem gen_of_iso {Y : Scheme.{0}} {F : X ⟶ X} {w : LB.Iso L (L.pull F)} (hw : PGen w) (h : Y ⟶ X) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![h ≫ F, h] ![1, -1]), t.IsGen := by
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L ![h ≫ F, h] j ≤ h ⁻¹ᵁ ((L.pull F).U (fun _ => j 0) ⊓ L.U (j 1)) := fun j y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.1 hy 0), Set.mem_iInter.1 hy 1⟩
  have v : ∀ (y : Y) (j : Fin 2 → L.ι), y ∈ LB.wchart L ![h ≫ F, h] j → gm (𝟙 Y) y (LB.wchart L ![h ≫ F, h] j)
      (res (le j) (pullU h _ (w.s (fun _ => j 0, j 1)))) = gw w h y (j 0) (j 1) := fun y j hy => gm_rp₁ h y _ _ (le j) hy _
  refine ⟨⟨fun j => res (le j) (pullU h _ (w.s (fun _ => j 0, j 1)))⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  refine (v y j hj).trans ((hw _ h y _ _ _ _ (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0) (Set.mem_iInter.1 hj 1)
    (Set.mem_iInter.1 hj' 1)).trans (congrArg₂ (· * ·) ?_ (v y j' hj').symm))
  rw [trF, Fin.prod_univ_two]
  simp only [Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]

theorem cst_comp {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  unfold cst gs spMap
  rw [dif_pos (by trivial), dif_pos (by trivial)]
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  first
  | (rw [key]; simp only [Scheme.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; rfl)
  | (rw [key]; rfl)
  | (rw [key]; simp only [Scheme.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; done)
  | (exact (key : False).elim)

theorem cst_not_isUnit {V : Type} [CommRing V] [IsLocalRing V] (p : X ⟶ Sp V) (x : X) (hx : p x = closedPoint V) {r : V}
    (hr : r ∈ maximalIdeal V) : ¬ IsUnit (cst p x r) := by
  intro hu
  have e : cst p x r = (p.stalkMap x).hom (((Sp V).presheaf.germ ⊤ (p x) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) := by
    unfold cst gs
    rw [dif_pos (by trivial)]
    have e' := congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r))
      (Scheme.Hom.germ_stalkMap p ⊤ x trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e'
    exact e'.symm
  rw [e] at hu
  have hu2 := isUnit_of_map_unit (p.stalkMap x).hom _ hu
  have hmem := ((Sp V).mem_basicOpen (U := ⊤) _ (p x) trivial).2 hu2
  have hb : (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = PrimeSpectrum.basicOpen r := by
    first
    | exact AlgebraicGeometry.basicOpen_eq_of_affine r
    | exact AlgebraicGeometry.Scheme.basicOpen_eq_of_affine r
    | exact AlgebraicGeometry.basicOpen_eq_of_affine' r
    | (simp; rfl)
    | (simp; exact rfl)
  rw [hb, hx] at hmem
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hmem hr

end Down

theorem principalPolarisation_exists_unique_section (hT : SecTwistSt) {K : Type} [Field K] (P : PolAV (Sp K)) :
    ∃ b : LB.Sec P.L, ∀ s : LB.Sec P.L, ∃! a : K, ∀ i, s.f i = constFn P.A.hom _ a * b.f i := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ P 1 le_rfl K (𝟙 _) 1
  let T : Over (Sp K) := Over.mk (𝟙 _)
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨w, hw⟩ := exists_iso_linComb (F := (snd T P.A).left) P.isLB (K := Fin 2)
    ![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1] (fun U _ k => by
      rw [e]; simp [Fin.prod_univ_succ])
  have hw' := (isGen_iff w).1 hw
  have hM := linComb_isLB P.L P.isLB (K := Fin 2) ![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left]
    ![((1 : ℕ) : ℤ) - 1, 1]
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  have mρ : ∀ (y : P.A.left) j, y ∈ P.L.U j → (snd T P.A).left (ρ.left y) ∈ P.L.U j := fun y j h =>
    (congrArg (fun q => q y ∈ P.L.U j) ρ₂).mpr h
  obtain ⟨w', hw₂⟩ := LBIso.chartPull (chartPullSec P.L _ ρ.left ρ₂) (chartPullPull _ ρ.left ρ.left rfl) (LBIso.symm ⟨w, hw⟩)
  obtain ⟨β, hβ⟩ := sec_pull_down ((isGen_iff w').1 hw₂) hM P.isLB (b i₀)

  have basis : ∀ t : LB.Sec (twistLB P.A P.L 1 (1 : T ⟶ P.A)), ∃ a : K, ∀ k, ∀ z ∈ (twistLB P.A P.L 1 (1 : T ⟶ P.A)).U k,
      gs (𝟙 _) z _ (t.f k) = cst (fst T P.A).left z a * gs (𝟙 _) z _ ((b i₀).f k) := fun t => by
    obtain ⟨r, hr, -⟩ := hb t
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (r i₀), fun k z hz => ?_⟩
    rw [hr k, su, gs_mul _ z _ hz, gs_res _ z _ hz, cst, Iso.hom_inv_id_apply]
    exact congrArg₂ (· * ·) ((gs_pull (𝟙 _) (fst T P.A).left z ⊤ trivial _).trans (by rw [Category.id_comp])) rfl
  have down : ∀ s : LB.Sec P.L, ∃ a : K, ∀ (y : P.A.left) j k, y ∈ P.L.U j →
      ρ.left y ∈ (twistLB P.A P.L 1 (1 : T ⟶ P.A)).U k → gs (𝟙 _) y _ (s.f j) =
        (gw w ρ.left y j k).val * (cst P.A.hom y a * gs ρ.left y _ ((b i₀).f k)) := fun s => by
    obtain ⟨t, ht⟩ := sec_pull_down hw' P.isLB hM s
    obtain ⟨a, ha⟩ := basis t
    refine ⟨a, fun y j k hj hk => ?_⟩
    have e₁ := ht _ ρ.left y j k (mρ y j hj) hk
    have e₂ := gs_of_id ρ.left y hk (ha k _ hk)
    rw [ρ₂] at e₁
    rw [ρ₁] at e₂
    exact e₁.trans (congrArg _ e₂)
  have nz : ¬ ∀ j, ∀ y ∈ P.L.U j, gs (𝟙 _) y _ (β.f j) = 0 := fun h0 => by
    have b0 : ∀ k, (b i₀).f k = 0 := fun k => fn_ext fun z hz => by
      obtain ⟨j, hj⟩ := exists_chart P.isLB ((snd T P.A).left z)
      have e₁ := hβ _ (snd T P.A).left z k j ((congrArg (fun q => q z ∈ (twistLB P.A P.L 1 (1 : T ⟶ P.A)).U k) ρ₃).mpr hz) hj
      rw [ρ₃, gs_stalkMap (snd T P.A).left z _ hj, h0 j _ hj, map_zero, mul_zero] at e₁
      rw [gs_eq _ z _ hz 0, map_zero, map_zero]; exact e₁
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have := (hu (fun _ => 0) fun k => (b0 k).trans ((su _).trans
      ((congrArg (_ * ·) (b0 k)).trans (mul_zero _))).symm).trans (hu (fun _ => 1) fun k => (b0 k).trans
      ((su _).trans ((congrArg (_ * ·) (b0 k)).trans (mul_zero _))).symm).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  obtain ⟨a₀, ha₀⟩ := down β
  have h₀ : a₀ ≠ 0 := fun h => nz fun j y hy => by
    obtain ⟨k, hk⟩ := exists_chart hM (ρ.left y)
    rw [ha₀ y j k hy hk, h, cst, map_zero, gs_eq _ y ⊤ trivial, map_zero, map_zero, zero_mul, mul_zero]
  refine ⟨β, fun s => ?_⟩
  obtain ⟨a, ha⟩ := down s
  refine ⟨a * a₀⁻¹, (sec_eq_iff _ _ _ _).2 fun j y hy => ?_, fun a' ha' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hM (ρ.left y)
    rw [ha y j k hy hk, ha₀ y j k hy hk, mul_left_comm (cst P.A.hom y _), ← _root_.mul_assoc (cst P.A.hom y _), ← cst_mul,
      inv_mul_cancel_right₀ h₀]
  · by_contra hne
    refine nz fun j y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (ρ.left y)
    have e₁ := (sec_eq_iff _ _ _ _).1 ha' j y hy
    have e₂ : gs (𝟙 _) y _ (s.f j) = cst P.A.hom y (a * a₀⁻¹) * gs (𝟙 _) y _ (β.f j) := by
      rw [ha y j k hy hk, ha₀ y j k hy hk, mul_left_comm (cst P.A.hom y _), ← _root_.mul_assoc (cst P.A.hom y _), ← cst_mul,
        inv_mul_cancel_right₀ h₀]
    have e₃ : cst P.A.hom y (a' - a * a₀⁻¹) * gs (𝟙 _) y _ (β.f j) = 0 := by rw [cst_sub, sub_mul, ← e₁, e₂, sub_self]
    rw [← _root_.one_mul (gs (𝟙 _) y _ (β.f j)), ← cst_one P.A.hom y, ← inv_mul_cancel₀ (sub_ne_zero.2 hne), cst_mul,
      _root_.mul_assoc, e₃, mul_zero]

def ThetaCoreSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (yt : Sp V ⟶ Y.X)
      (z : Sp (FractionRing V) ⟶ Xo.XF c), z ≫ Y.j = spMap (algebraMap V (FractionRing V)) ≫ yt →
      ∀ (G : SAB H (Sp V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp (FractionRing V)))
        (m2 : SABMap t' G (spMap (algebraMap V (FractionRing V)))),
        ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : V, ∀ i, σ.f i = constFn G.G.hom _ a * θ.f i) ∧
          (∃ (g : G.G.left) (i : G.PP.L.ι), G.G.hom g = closedPoint V ∧ g ∈ G.G.left.basicOpen (θ.f i)) ∧
          ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L), IsRigIso m2.cm t'.PP G.PP w2 ∧
            (∀ (j : G.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens) (h₁ : W ≤ m2.φ ⁻¹ᵁ G.PP.L.U j)
              (h₂ : W ≤ (G.PP.L.pull m2.φ).U (fun _ => j) ⊓ t'.PP.L.U k),
              (m2.φ.appLE _ _ h₁).hom (θ.f j) =
                resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k)) ∧
            ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i

theorem globalSections_rank_one_fibre (hT : SecTwistSt) (hA : AmplePtSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    {K : Type} [Field K] {z : Sp K ⟶ S} {t' : SAB H (Sp K)} (m : SABMap t' o.t z) :
    ∃ β : LB.Sec t'.PP.L, ∀ s : LB.Sec t'.PP.L, ∃! a : K, ∀ i, s.f i = constFn t'.G.hom _ a * β.f i := by
  have := t'.semi.smooth
  obtain ⟨w, g, -⟩ := m.lin
  obtain ⟨am, kt⟩ := hA _ _ z _ _ m.φ m.cart _ _ o.t.PP.isLB t'.PP.isLB ⟨w, g⟩ o.ample o.ktriv
  have := t'.semi.geomConnected
  have : ConnectedSpace t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  exact principalPolarisation_exists_unique_section hT
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 o.proper, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

theorem thetaCore (hT : SecTwistSt) (hA : AmplePtSt) : ThetaCoreSt := by
  intro E _ _ _ H D l Xo c O _ β Y hP V _ _ _ yt z hz G m t' m2
  have := G.semi.smooth
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m2
  have cancel : ∀ (p : Sp (FractionRing V) ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p), Nonempty (SABMap t' Y.oF.t z) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m3⟩ := cancel _ hz.symm n
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre hT hA Y.oF m3
  obtain ⟨V₀, hV₀, θ₀, hθ₀, -, nz⟩ := hP (yt (closedPoint V))
  have mem : ∀ x, m.φ x ∈ Y.t.G.hom ⁻¹ᵁ V₀ := fun x => (congrArg (fun q => q x ∈ V₀) m.cart.1.w).mpr
    ((congrArg (fun U => G.G.hom x ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem yt hV₀)).mpr trivial)
  have le : ∀ j, m.φ ⁻¹ᵁ Y.t.PP.L.U j ≤ m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ V₀ ⊓ Y.t.PP.L.U j) := fun j x hx => ⟨mem x, hx⟩
  have ev : ∀ y j, m.φ y ∈ Y.t.PP.L.U j → gs (𝟙 _) y _ ((m.φ.appLE _ _ (le j)).hom (θ₀ j)) = gs m.φ y _ (θ₀ j) :=
    fun y j h => (gs_appLE m.φ _ _ (le j) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  obtain ⟨w1, g1, -⟩ := m.lin
  obtain ⟨θ, hθ⟩ := sec_down ((isGen_iff w1).1 g1) Y.t.PP.isLB G.PP.isLB (fun j => (m.φ.appLE _ _ (le j)).hom (θ₀ j))
    fun y j j' h h' => by
      have hm : m.φ y ∈ Y.t.G.hom ⁻¹ᵁ V₀ ⊓ Y.t.PP.L.U j ⊓ Y.t.PP.L.U j' := ⟨⟨mem y, h⟩, h'⟩
      have e := congrArg (gs m.φ y _) (hθ₀ j j')
      rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y (Y.t.PP.L.U j ⊓ Y.t.PP.L.U j') ⟨h, h'⟩] at e
      exact (ev y j h).trans (e.trans (congrArg _ (ev y j' h').symm))
  obtain ⟨g₀, i, hg₀, hb₀⟩ := nz _ hV₀
  obtain ⟨g, hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 g₀ (closedPoint V) hg₀
  obtain rfl : m.φ g = g₀ := hg₁
  have hgi : m.φ g ∈ Y.t.G.hom ⁻¹ᵁ V₀ ⊓ Y.t.PP.L.U i := Y.t.G.left.basicOpen_le _ hb₀
  obtain ⟨k₀, hk₀⟩ := exists_chart G.PP.isLB g
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    have u₀ : IsUnit (gs (𝟙 _) (m.φ g) _ (θ₀ i)) := by
      rw [gs_eq (𝟙 _) (m.φ g) _ hgi]; exact (Y.t.G.left.mem_basicOpen _ _ hgi).1 hb₀
    have u₁ : IsUnit (gs m.φ g _ (θ₀ i)) := by rw [gs_stalkMap m.φ g _ hgi]; exact u₀.map _
    rw [← ev g i hgi.2, hθ _ (𝟙 _) g i k₀ hgi.2 hk₀] at u₁
    exact isUnit_of_mul_isUnit_right u₁
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  have down := sec_pull_down ((isGen_iff w2).1 g2) G.PP.isLB t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant m2.φ := IsSchemeTheoreticallyDominant.of_isPullback m2.cart.1.flip
  have : QuasiCompact m2.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) m2.cart.1.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f σ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f τ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn t'.G.hom _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn G.G.hom _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine m2.φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB y
    refine (gs_pull (𝟙 _) m2.φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) m2.φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ m2.φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ m2.φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk, (sec_eq_iff _ _ _ _).1 h₃ k y hk,
      Category.id_comp, m2.cart.1.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : LB.Sec t'.PP.L} {a a' : FractionRing V}, (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      (∀ k, t.f k = constFn t'.G.hom _ a' * u.f k) → ∀ k, s.f k = constFn t'.G.hom _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : LB.Sec t'.PP.L} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      ∀ k, t.f k = constFn t'.G.hom _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : LB.Sec G.PP.L) (r : V), (∀ j, θ.f j = constFn G.G.hom _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit G.G.hom g hg₂ hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀, -⟩ := hb σ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ σ' σ' 0 hσ' hσ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  have gen : ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := fun s' => by
    obtain ⟨a, ha, hu⟩ := hb s'
    refine ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀), fun a' ha' => ?_⟩
    rw [← hu _ (mulc ha' ha₀), mul_inv_cancel_right₀ h₀]
  refine ⟨θ, fun σ => ?_, ⟨g, k₀, hg₂, (G.G.left.mem_basicOpen _ _ hk₀).2 (by rwa [gs_eq _ _ _ hk₀] at un)⟩, w2, σ', ⟨g2, r2⟩,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, gen⟩
  · obtain ⟨σK, hσK⟩ := down σ
    obtain ⟨a, ha, -⟩ := gen σK
    have ex : ∃ r : V, ∀ i, σ.f i = constFn G.G.hom _ r * θ.f i := by
      by_cases h : IsLocalization.IsInteger V a
      · obtain ⟨r, rfl⟩ := h
        exact ⟨r, inj σ θ σK σ' r hσK hσ' ha⟩
      · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
        obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
        obtain ⟨u, rfl⟩ := unit σ r (inj θ σ σ' σK r hσ' hσK (hr ▸ invc hne ha))
        exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
    obtain ⟨r, hr⟩ := ex
    refine ⟨r, hr, fun r' hr' => ?_⟩
    by_contra hne
    have e : cst G.G.hom g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst G.G.hom g (r' - r) * 0 := by
      rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
    exact un.ne_zero (cst_regular G.G.hom g (sub_ne_zero.2 hne) e)
  · rw [gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy, hσ' _ (𝟙 _) y j k (h₁ hy) (h₂ hy).2, gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg₂ (· * ·) ((gs_res (𝟙 _) y h₂ hy _).trans (gs_unit (𝟙 _) y _ (h₂ hy) _)).symm rfl

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

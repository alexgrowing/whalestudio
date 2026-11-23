import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.RigidTriv

variable {X Y Z : Scheme.{0}}

theorem gm_stalk (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    gm f z U a = Units.map (f.stalkMap z).hom.toMonoidHom (gm (𝟙 Y) (f z) U a) := by
  ext1
  simp [gm, h, pullU]
  exact (Scheme.Hom.germ_stalkMap_apply f U z h _).symm

theorem gm_pull_id (g : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : g z ∈ U) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Z) z (g ⁻¹ᵁ U) (pullU g U a) = gm g z U a := by
  ext1
  simp [gm, h, pullU]
  rfl

private lemma gm_id_val_eq_germ (W : Z.Opens) (z : Z) (hz : z ∈ W) (u : Γ(Z, W)ˣ) :
    Units.val (gm (𝟙 Z) z W u) = (Z.presheaf.germ W z hz).hom u.1 := by
  simp [gm, hz, pullU]
  rfl

private lemma gm_val_eq_germ_app (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    Units.val (gm f z U a) = (Z.presheaf.germ (f ⁻¹ᵁ U) z h).hom (f.app U a.1) := by
  simp [gm, h, pullU]

private lemma gm_res_lemma_4 {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm (𝟙 Y) y U a := by
  ext1
  rw [gm_id_val_eq_germ V y hy, gm_id_val_eq_germ U y (hVU hy)]
  exact TopCat.Presheaf.germ_res_apply ..

private lemma gm_units_map_restrict (f : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hVU : V ≤ U) (hz : f z ∈ V) (a : Γ(Y, U)ˣ) :
    gm f z V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm f z U a := by
  rw [gm_stalk f z V hz, gm_stalk f z U (hVU hz), gm_res_lemma_4 hVU (f z) hz]

private lemma units_eq_of_gm_id_eq_on_open {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x, x ∈ O → gm (𝟙 X) x O a = gm (𝟙 X) x O b) : a = b := by
  ext1
  refine TopCat.Presheaf.section_ext X.sheaf O _ _ fun x hx => ?_
  have hv := congrArg Units.val (h x hx)
  rw [gm_id_val_eq_germ O x hx, gm_id_val_eq_germ O x hx] at hv
  exact hv

private lemma exists_unit_on_open_of_gm_agree_on_cover (V : X.Opens) {κ : Type} (O : κ → X.Opens) (hO : ∀ a, O a ≤ V)
    (hcov : ∀ x ∈ V, ∃ a, x ∈ O a) (u : ∀ a, Γ(X, O a)ˣ)
    (hu : ∀ a b x (_ : x ∈ O a) (_ : x ∈ O b), gm (𝟙 X) x (O a) (u a) = gm (𝟙 X) x (O b) (u b)) :
    ∃ d : Γ(X, V)ˣ, ∀ a x, x ∈ O a → gm (𝟙 X) x V d = gm (𝟙 X) x (O a) (u a) := by
  have hcover : V ≤ iSup O := fun x hx => by
    obtain ⟨a, ha⟩ := hcov x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
  have compat : ∀ w : ∀ a, Γ(X, O a), (∀ a b x (ha : x ∈ O a) (hb : x ∈ O b),
      (X.presheaf.germ (O a) x ha).hom (w a) = (X.presheaf.germ (O b) x hb).hom (w b)) →
      TopCat.Presheaf.IsCompatible X.sheaf.1 O w := by
    intro w hw a b
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
    exact (TopCat.Presheaf.germ_res_apply X.presheaf _ x hx (w a)).trans
      ((hw a b x hx.1 hx.2).trans (TopCat.Presheaf.germ_res_apply X.presheaf _ x hx (w b)).symm)
  have hval : ∀ a b x (ha : x ∈ O a) (hb : x ∈ O b),
      (X.presheaf.germ (O a) x ha).hom (u a).1 = (X.presheaf.germ (O b) x hb).hom (u b).1 := by
    intro a b x ha hb
    have hv := congrArg Units.val (hu a b x ha hb)
    rw [gm_id_val_eq_germ _ x ha, gm_id_val_eq_germ _ x hb] at hv
    exact hv
  have hinv : ∀ a b x (ha : x ∈ O a) (hb : x ∈ O b),
      (X.presheaf.germ (O a) x ha).hom (u a)⁻¹.1 = (X.presheaf.germ (O b) x hb).hom (u b)⁻¹.1 := by
    intro a b x ha hb
    have hv := congrArg Units.val (congrArg (·⁻¹) (hu a b x ha hb))
    rw [← map_inv, ← map_inv, gm_id_val_eq_germ _ x ha, gm_id_val_eq_germ _ x hb] at hv
    exact hv
  obtain ⟨d0, hd0, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf O V (fun a => homOfLE (hO a)) hcover
    (fun a => (u a).1) (compat _ hval)
  obtain ⟨d1, hd1, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf O V (fun a => homOfLE (hO a)) hcover
    (fun a => (u a)⁻¹.1) (compat _ hinv)
  have g0 : ∀ a x (hx : x ∈ O a), (X.presheaf.germ V x (hO a hx)).hom d0 = (X.presheaf.germ (O a) x hx).hom (u a).1 :=
    fun a x hx => (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hO a)) x hx d0).symm.trans
      (congrArg (X.presheaf.germ (O a) x hx).hom (hd0 a))
  have g1 : ∀ a x (hx : x ∈ O a), (X.presheaf.germ V x (hO a hx)).hom d1 = (X.presheaf.germ (O a) x hx).hom (u a)⁻¹.1 :=
    fun a x hx => (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hO a)) x hx d1).symm.trans
      (congrArg (X.presheaf.germ (O a) x hx).hom (hd1 a))
  have h01 : d0 * d1 = 1 := TopCat.Presheaf.section_ext X.sheaf V _ _ fun x hx => by
    obtain ⟨a, ha⟩ := hcov x hx
    exact calc (X.presheaf.germ V x hx).hom (d0 * d1)
          = (X.presheaf.germ V x hx).hom d0 * (X.presheaf.germ V x hx).hom d1 := RingHom.map_mul _ _ _
      _ = (X.presheaf.germ (O a) x ha).hom (u a).1 * (X.presheaf.germ (O a) x ha).hom (u a)⁻¹.1 := by
          rw [g0 a x ha, g1 a x ha]
      _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      _ = (X.presheaf.germ V x hx).hom 1 := (map_one _).symm
  refine ⟨⟨d0, d1, h01, (mul_comm (d1 : Γ(X, V)) d0).trans h01⟩, fun a x hx => ?_⟩
  ext1
  rw [gm_id_val_eq_germ V x (hO a hx), gm_id_val_eq_germ (O a) x hx]
  exact g0 a x hx

private lemma gm_comp_eq_gm_pullU (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (U : Z.Opens) (h : f x ∈ g ⁻¹ᵁ U) (a : Γ(Z, U)ˣ) :
    gm (f ≫ g) x U a = gm f x (g ⁻¹ᵁ U) (pullU g U a) := by
  ext1
  rw [gm_val_eq_germ_app (f ≫ g) x U h, gm_val_eq_germ_app f x (g ⁻¹ᵁ U) h]
  simp [pullU]
  rfl

private lemma germ_appLE_unit_eq_gm_val (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V)
    (a : Γ(Y, U)ˣ) : (X.presheaf.germ V x hx).hom ((f.appLE U V hVU).hom a.1) = Units.val (gm f x U a) := by
  rw [gm_val_eq_germ_app f x U (hVU hx)]
  exact TopCat.Presheaf.germ_res_apply ..

private lemma exists_mem_U_of_isLB {N : LB Y} (hN : N.IsLB) (y : Y) : ∃ i, y ∈ N.U i := by
  have hy : y ∈ (⊤ : Y.Opens) := trivial
  rw [← hN.cover] at hy
  exact TopologicalSpace.Opens.mem_iSup.1 hy

private lemma gm_id_res {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (res hVU a) = gm (𝟙 Y) y U a :=
  gm_res_lemma_4 hVU y hy a

theorem pull_gen {N : LB Y} {F : Z ⟶ Y} {t : (N.pull F).Gen} (ht : t.IsGen) (z : Z) (i j : N.ι)
    (hi : F z ∈ N.U i) (hj : F z ∈ N.U j) :
    gm (𝟙 Z) z ((N.pull F).U (fun _ => i)) (t.s fun _ => i) =
      gm F z (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Z) z ((N.pull F).U (fun _ => j)) (t.s fun _ => j) := by
  have hz : z ∈ (N.pull F).U (fun _ => i) ⊓ (N.pull F).U (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have hij : F z ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  have H := congrArg (fun u => (Z.presheaf.germ _ z hz).hom (Units.val u)) (ht (fun _ => i) (fun _ => j))
  ext1
  rw [Units.val_mul, gm_id_val_eq_germ _ z hz.1, gm_id_val_eq_germ _ z hz.2, gm_val_eq_germ_app F z _ hij]
  simp only [res, Units.coe_map, Units.val_mul, map_mul, MonoidHom.coe_coe, TopCat.Presheaf.germ_res_apply] at H
  have hg : (Z.presheaf.germ _ z hz).hom ((N.pull F).g (fun _ => i) (fun _ => j)).1 =
      (Z.presheaf.germ (F ⁻¹ᵁ (N.U i ⊓ N.U j)) z hij).hom (F.app _ (N.g i j).1) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    exact TopCat.Presheaf.germ_res_apply ..
  rw [hg] at H
  exact H

def LocGen (N : LB Y) (W : Y.Opens) (s : ∀ i, Γ(Y, W ⊓ N.U i)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : N.ι), f z ∈ W → f z ∈ N.U i → f z ∈ N.U j →
    gm f z (W ⊓ N.U i) (s i) = gm f z (N.U i ⊓ N.U j) (N.g i j) * gm f z (W ⊓ N.U j) (s j)

theorem exists_locGen {N : LB Y} (W : Y.Opens) {t : (N.pull W.ι).Gen} (ht : t.IsGen) :
    ∃ s, LocGen N W s := by
  choose b hb using fun i => exists_ext_unit W.ι ((N.pull W.ι).U fun _ => i) (t.s fun _ => i)
  have hle : ∀ i, W ⊓ N.U i ≤ W.ι ''ᵁ ((N.pull W.ι).U fun _ => i) := fun i y hy =>
    (Scheme.Opens.mem_ι_image_iff (x := ⟨y, hy.1⟩)).2 (Set.mem_iInter.2 fun _ => hy.2)
  have key : ∀ (y : Y) (hyW : y ∈ W) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j),
      gm (𝟙 Y) y _ (b i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y _ (b j) := by
    intro y hyW i j hi hj
    obtain ⟨z0, rfl⟩ : ∃ z0 : W.toScheme, W.ι z0 = y := ⟨⟨y, hyW⟩, rfl⟩
    have hz0i : z0 ∈ (N.pull W.ι).U fun _ => i := Set.mem_iInter.2 fun _ => hi
    have hz0j : z0 ∈ (N.pull W.ι).U fun _ => j := Set.mem_iInter.2 fun _ => hj
    have P := pull_gen ht z0 i j hi hj
    rw [← hb i W.toScheme (𝟙 _) z0 hz0i, ← hb j W.toScheme (𝟙 _) z0 hz0j, Category.id_comp,
      gm_stalk W.ι z0 _ (hle i ⟨hyW, hi⟩), gm_stalk W.ι z0 _ (hle j ⟨hyW, hj⟩),
      gm_stalk W.ι z0 _ (show W.ι z0 ∈ N.U i ⊓ N.U j from ⟨hi, hj⟩), ← map_mul] at P
    exact Units.map_injective (fun a c h => (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z0)).1 h) P
  refine ⟨fun i => Units.map (Y.presheaf.map (homOfLE (hle i)).op).hom.toMonoidHom (b i), ?_⟩
  intro Z f z i j hW hi hj
  rw [gm_stalk f z _ (show f z ∈ W ⊓ N.U i from ⟨hW, hi⟩), gm_stalk f z _ (show f z ∈ N.U i ⊓ N.U j from ⟨hi, hj⟩),
    gm_stalk f z _ (show f z ∈ W ⊓ N.U j from ⟨hW, hj⟩), ← map_mul, gm_res_lemma_4 (hle i) _ ⟨hW, hi⟩,
    gm_res_lemma_4 (hle j) _ ⟨hW, hj⟩, key (f z) hW i j hi hj]

theorem sec_mem {p : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ p = 𝟙 X) {V : X.Opens} {x : X} (hx : x ∈ V) :
    e x ∈ p ⁻¹ᵁ V := by
  have hpe : p (e x) = x := by rw [← Scheme.Hom.comp_apply, he]; rfl
  change p (e x) ∈ V
  rwa [hpe]

theorem exists_normalised {N : LB Y} (hN : N.IsLB) {p : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ p = 𝟙 X)
    {r : (N.pull e).Gen} (hr : r.IsGen) (V : X.Opens) {s : ∀ i, Γ(Y, p ⁻¹ᵁ V ⊓ N.U i)ˣ}
    (hs : LocGen N (p ⁻¹ᵁ V) s) :
    ∃ s', LocGen N (p ⁻¹ᵁ V) s' ∧ ∀ x ∈ V, ∀ i, e x ∈ N.U i →
      gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s' i) = gm (𝟙 X) x ((N.pull e).U (fun _ => i)) (r.s fun _ => i) := by
  have hOe : ∀ i, V ⊓ ((N.pull e).U fun _ => i) ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ N.U i) := fun i x hx =>
    (show e x ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨sec_mem he hx.1, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
  have hOr : ∀ i, V ⊓ ((N.pull e).U fun _ => i) ≤ (N.pull e).U fun _ => i := fun i => inf_le_right
  have gmu : ∀ i x (hx : x ∈ V ⊓ ((N.pull e).U fun _ => i)),
      gm (𝟙 X) x _ (Units.map (X.presheaf.map (homOfLE (hOr i)).op).hom.toMonoidHom (r.s fun _ => i) /
        Units.map (X.presheaf.map (homOfLE (hOe i)).op).hom.toMonoidHom (pullU e _ (s i))) =
      gm (𝟙 X) x _ (r.s fun _ => i) / gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s i) := by
    intro i x hx
    rw [map_div, gm_res_lemma_4 (hOr i) x hx, gm_res_lemma_4 (hOe i) x hx, gm_pull_id e x _ (hOe i hx)]
  obtain ⟨d, hd⟩ := exists_unit_on_open_of_gm_agree_on_cover V (fun i => V ⊓ ((N.pull e).U fun _ => i)) (fun i => inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_mem_U_of_isLB hN (e x)
      exact ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩)
    (fun i => Units.map (X.presheaf.map (homOfLE (hOr i)).op).hom.toMonoidHom (r.s fun _ => i) /
        Units.map (X.presheaf.map (homOfLE (hOe i)).op).hom.toMonoidHom (pullU e _ (s i)))
    (by
      intro i j x hi hj
      rw [gmu i x hi, gmu j x hj]
      have hxi : e x ∈ p ⁻¹ᵁ V ⊓ N.U i := hOe i hi
      have hxj : e x ∈ p ⁻¹ᵁ V ⊓ N.U j := hOe j hj
      rw [pull_gen hr x i j hxi.2 hxj.2, hs X e x i j hxi.1 hxi.2 hxj.2, mul_div_mul_left_eq_div])
  refine ⟨fun i => Units.map (Y.presheaf.map (homOfLE (inf_le_left : p ⁻¹ᵁ V ⊓ N.U i ≤ p ⁻¹ᵁ V)).op).hom.toMonoidHom
    (pullU p V d) * s i, ?_, ?_⟩
  · intro Z f z i j hW hi hj
    rw [map_mul, map_mul, gm_units_map_restrict f z inf_le_left (show f z ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨hW, hi⟩),
      gm_units_map_restrict f z inf_le_left (show f z ∈ p ⁻¹ᵁ V ⊓ N.U j from ⟨hW, hj⟩), hs Z f z i j hW hi hj, mul_left_comm]
  · intro x hx i hi
    have hxO : x ∈ V ⊓ ((N.pull e).U fun _ => i) := ⟨hx, Set.mem_iInter.2 fun _ => hi⟩
    rw [map_mul, gm_units_map_restrict e x inf_le_left (show e x ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨sec_mem he hx, hi⟩),
      ← gm_comp_eq_gm_pullU e p x V (sec_mem he hx) d, he, hd i x hxO, gmu i x hxO, div_mul_cancel]

theorem agree_of_rigid {N : LB Y} (hN : N.IsLB) {p : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ p = 𝟙 X)
    (rig : ∀ (V : X.Opens) (u : Γ(Y, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1)
    {V V' : X.Opens} {s : ∀ i, Γ(Y, p ⁻¹ᵁ V ⊓ N.U i)ˣ} {s' : ∀ i, Γ(Y, p ⁻¹ᵁ V' ⊓ N.U i)ˣ}
    (hs : LocGen N (p ⁻¹ᵁ V) s) (hs' : LocGen N (p ⁻¹ᵁ V') s')
    (h : ∀ x, x ∈ V → x ∈ V' → ∀ i, e x ∈ N.U i →
      gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s i) = gm e x (p ⁻¹ᵁ V' ⊓ N.U i) (s' i))
    (y : Y) (hy : p y ∈ V) (hy' : p y ∈ V') (i : N.ι) (hi : y ∈ N.U i) :
    gm (𝟙 Y) y (p ⁻¹ᵁ V ⊓ N.U i) (s i) = gm (𝟙 Y) y (p ⁻¹ᵁ V' ⊓ N.U i) (s' i) := by
  have h1 : ∀ i, p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i ≤ p ⁻¹ᵁ V ⊓ N.U i := fun i y hy =>
    (show y ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨(show p y ∈ V ⊓ V' from hy.1).1, hy.2⟩)
  have h2 : ∀ i, p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i ≤ p ⁻¹ᵁ V' ⊓ N.U i := fun i y hy =>
    (show y ∈ p ⁻¹ᵁ V' ⊓ N.U i from ⟨(show p y ∈ V ⊓ V' from hy.1).2, hy.2⟩)
  have gmw : ∀ i y (hy : y ∈ p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i),
      gm (𝟙 Y) y _ (Units.map (Y.presheaf.map (homOfLE (h1 i)).op).hom.toMonoidHom (s i) /
        Units.map (Y.presheaf.map (homOfLE (h2 i)).op).hom.toMonoidHom (s' i)) =
      gm (𝟙 Y) y _ (s i) / gm (𝟙 Y) y _ (s' i) := by
    intro i y hy
    rw [map_div, gm_res_lemma_4 (h1 i) y hy, gm_res_lemma_4 (h2 i) y hy]
  obtain ⟨c, hc⟩ := exists_unit_on_open_of_gm_agree_on_cover (p ⁻¹ᵁ (V ⊓ V')) (fun i => p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i) (fun i => inf_le_left)
    (fun y hy => by
      obtain ⟨i, hi⟩ := exists_mem_U_of_isLB hN y
      exact ⟨i, hy, hi⟩)
    (fun i => Units.map (Y.presheaf.map (homOfLE (h1 i)).op).hom.toMonoidHom (s i) /
        Units.map (Y.presheaf.map (homOfLE (h2 i)).op).hom.toMonoidHom (s' i))
    (by
      intro i j y hi hj
      rw [gmw i y hi, gmw j y hj]
      have a1 := h1 i hi
      have a2 := h2 i hi
      have b1 := h1 j hj
      have b2 := h2 j hj
      rw [hs Y (𝟙 Y) y i j a1.1 a1.2 b1.2, hs' Y (𝟙 Y) y i j a2.1 a2.2 b2.2, mul_div_mul_left_eq_div])
  have hle : V ⊓ V' ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V ⊓ V')) := fun x hx => sec_mem he hx
  have c1 : c.1 = 1 := rig (V ⊓ V') c.1 hle (TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => by
    obtain ⟨i, hi⟩ := exists_mem_U_of_isLB hN (e x)
    have hxO : e x ∈ p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i := ⟨hle hx, hi⟩
    have hx' : x ∈ V ⊓ V' := hx
    have hgm : gm e x (p ⁻¹ᵁ (V ⊓ V')) c = 1 := by
      rw [gm_stalk e x _ (hle hx), hc i (e x) hxO, gmw i (e x) hxO, map_div, ← gm_stalk e x _ (h1 i hxO),
        ← gm_stalk e x _ (h2 i hxO), h x hx'.1 hx'.2 i hi, div_self']
    exact (germ_appLE_unit_eq_gm_val e _ _ hle x hx c).trans (by rw [hgm, Units.val_one]; exact (RingHom.map_one _).symm))
  have hyc : y ∈ p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i := ⟨(show p y ∈ V ⊓ V' from ⟨hy, hy'⟩), hi⟩
  have key := hc i y hyc
  rw [gmw i y hyc, show c = 1 from Units.ext c1, map_one] at key
  exact (div_eq_one.1 key.symm)

theorem exists_gen_of_rigid : ∀ (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (N : LB P.left), e ≫ P.hom = 𝟙 X → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → N.IsLB → (∃ r : (N.pull e).Gen, r.IsGen) → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ t : (N.pull (P.hom ⁻¹ᵁ V).ι).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X P e N he rig hN hr0 hloc
  obtain ⟨r, hr⟩ := hr0
  choose V hxV t ht using hloc
  choose s hs using fun x => exists_locGen (P.hom ⁻¹ᵁ V x) (ht x)
  choose s' hs' hn using fun x => exists_normalised hN he hr (V x) (hs x)
  have glue_i : ∀ i, ∃ T : Γ(P.left, N.U i)ˣ, ∀ x y, y ∈ P.hom ⁻¹ᵁ V x ⊓ N.U i →
      gm (𝟙 _) y (N.U i) T = gm (𝟙 _) y (P.hom ⁻¹ᵁ V x ⊓ N.U i) (s' x i) := fun i =>
    exists_unit_on_open_of_gm_agree_on_cover (N.U i) (fun x => P.hom ⁻¹ᵁ V x ⊓ N.U i) (fun x => inf_le_right)
      (fun y hy => ⟨P.hom y, (show y ∈ P.hom ⁻¹ᵁ V (P.hom y) ⊓ N.U i from ⟨hxV (P.hom y), hy⟩)⟩)
      (fun x => s' x i)
      (fun x x' y hx hx' => agree_of_rigid hN he rig (hs' x) (hs' x')
        (fun x0 h0 h0' j hj => (hn x x0 h0 j hj).trans (hn x' x0 h0' j hj).symm) y hx.1 hx'.1 i hx.2)
  choose T hT using glue_i
  refine ⟨⟨T⟩, fun i j => ?_⟩
  apply units_eq_of_gm_id_eq_on_open
  intro y hy
  have hy' : y ∈ N.U i ⊓ N.U j := hy
  have hx : y ∈ P.hom ⁻¹ᵁ V (P.hom y) := hxV (P.hom y)
  dsimp only
  rw [map_mul, gm_id_res _ y hy', gm_id_res _ y hy', hT i _ y ⟨hx, hy'.1⟩, hT j _ y ⟨hx, hy'.2⟩]
  exact hs' (P.hom y) P.left (𝟙 _) y i j hx hy'.1 hy'.2

end GlobalTheory.RigidTriv

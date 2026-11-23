import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqSingleOfIsUnitCoeff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusPic

open GlobalTheory.UU GlobalTheory.UU.PackageDescent

section Ratio

variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_unit_ratio {L : LB X} (hL : L.IsLB) {φ φ' : K → (Y ⟶ X)} (hφ : φ = φ') {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ ε)) (ha : a.IsGen) (b : LB.Gen (LB.LinComb L φ' ε)) (hb : b.IsGen) :
    ∃ v : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val a r z J = gm r z ⊤ v * val b r z J := by
  subst hφ
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ a (LB.invGen L _ _ b))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ha (DVR.invGen_isGen _ _ _ _ hb))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e : gm r z ⊤ (res le (t.s PEmpty.elim)) = val a r z J * (val b r z J)⁻¹ := by
    refine (gm_res r z le trivial _).trans ?_
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ]
    exact (val_of t r z J PEmpty.elim (fun k => k.elim)).symm
  rw [e, inv_mul_cancel_right]

theorem gm_pullTop (g : Z ⟶ Y) (p : Y ⟶ X) (z : Z) (f : Γ(X, ⊤)ˣ) :
    gm g z ⊤ (Units.map p.appTop.hom.toMonoidHom f) = gm (g ≫ p) z ⊤ f :=
  gm_pull g p z ⊤ trivial f

end Ratio

section Points

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G Y : Over S} [GrpObj G]

def act (i : splitTorus S X ⟶ G) (Y : Over S) : splitTorus S X ⊗ (G ⊗ Y) ⟶ G ⊗ Y :=
  lift ((fst _ _ ≫ i) * (snd _ _ ≫ fst G Y)) (snd _ _ ≫ snd G Y)

theorem lift_act (i : splitTorus S X ⟶ G) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) :
    lift t (lift g y) ≫ act i Y = lift ((t ≫ i) * g) y := by
  simp [act, comp_lift, MonObj.comp_mul]

def sec (G : Over S) (y₀ : 𝟙_ (Over S) ⟶ Y) : G ⟶ G ⊗ Y := lift (𝟙 G) (toUnit G ≫ y₀)

theorem comp_sec {Z : Over S} (g : Z ⟶ G) (y₀ : 𝟙_ (Over S) ⟶ Y) :
    g ≫ sec G y₀ = lift g (toUnit Z ≫ y₀) := by
  simp [sec, comp_lift]

variable [Module.Free ℤ X] {X' : Scheme.{0}}

theorem exists_weight [ConnectedSpace (G ⊗ Y).left] [IsReduced (G ⊗ Y).left]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (P : (G ⊗ Y).left ⟶ X')
    (hP : (act i Y).left ≫ P = (snd (splitTorus S X) (G ⊗ Y)).left ≫ P)
    {N : LB X'} (hN : N.IsLB) (u : LB.Gen (N.pull P)) (hu : u.IsGen) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val u (lift ((t ≫ i) * g) y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * val u (lift g y).left z J := by
  obtain ⟨v, hv⟩ := exists_unit_ratio hN (φ := fun _ : PUnit => (act i Y).left ≫ P)
    (φ' := fun _ => (snd (splitTorus S X) (G ⊗ Y)).left ≫ P) (funext fun _ => hP) (ε := fun _ => 1)
    (LB.pullGen N _ _ u (act i Y).left) (DVR.pullGen_isGen _ _ _ _ hu _)
    (LB.pullGen N _ _ u (snd (splitTorus S X) (G ⊗ Y)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨χ, hχ⟩ := GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul S X (G ⊗ Y) v
  refine ⟨χ, fun Z t g y z J hJ => ?_⟩
  have key : ∀ t' : Z ⟶ splitTorus S X, val u (lift ((t' ≫ i) * g) y).left z J =
      gm (lift t' (lift g y)).left z ⊤ v * val u (lift g y).left z J := by
    intro t'
    have h := hv Z.left (lift t' (lift g y)).left z J hJ
    rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, lift_act, lift_snd] at h
    exact h
  have h1 : gm (lift (1 : Z ⟶ splitTorus S X) (lift g y)).left z ⊤ v = 1 := by
    have h := key 1
    rw [MonObj.one_comp, _root_.one_mul] at h
    exact mul_eq_right.1 h.symm
  have h2 : Units.map (lift t (lift g y)).left.appTop.hom.toMonoidHom v = chV t χ *
      Units.map (lift (1 : Z ⟶ splitTorus S X) (lift g y)).left.appTop.hom.toMonoidHom v :=
    Units.ext (hχ Z t (lift g y))
  rw [key t, gm_top _ z v, h2, map_mul, ← gm_top, h1, _root_.mul_one]

theorem exists_unit_weight {B : Over S} (i : splitTorus S X ⟶ G) (q : G ⟶ B)
    (hiq : ∀ {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q)
    (P : (G ⊗ Y).left ⟶ X') (E : B.left ⟶ X') (y₀ : 𝟙_ (Over S) ⟶ Y)
    (hE : (sec G y₀).left ≫ P = q.left ≫ E)
    {N : LB X'} (hN : N.IsLB) (u : LB.Gen (N.pull P)) (hu : u.IsGen) (s : LB.Gen (N.pull E)) (hs : s.IsGen)
    (χ : X) (hw : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val u (lift ((t ≫ i) * g) y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * val u (lift g y).left z J) :
    ∃ f : Γ(G.left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left),
      gm ((t ≫ i) * g).left z ⊤ f = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z ⊤ f := by
  obtain ⟨f, hf⟩ := exists_unit_ratio hN (φ := fun _ : PUnit => (sec G y₀).left ≫ P)
    (φ' := fun _ => q.left ≫ E) (funext fun _ => hE) (ε := fun _ => 1)
    (LB.pullGen N _ _ u (sec G y₀).left) (DVR.pullGen_isGen _ _ _ _ hu _)
    (LB.pullGen N _ _ s q.left) (DVR.pullGen_isGen _ _ _ _ hs _)
  refine ⟨f, fun Z t g z => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_pt hN z
  have a := hf Z.left ((t ≫ i) * g).left z J hJ
  have b := hf Z.left g.left z J hJ
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_sec, hiq] at a
  rw [val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_sec] at b
  have c := hw Z t g (toUnit Z ≫ y₀) z J hJ
  rw [a, b, ← _root_.mul_assoc] at c
  exact mul_right_cancel c

end Points

section Main

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B Y : Over S} [GrpObj G]

abbrev proj (q : G ⟶ B) (Y : Over S) : G ⊗ Y ⟶ B ⊗ Y := lift (fst G Y ≫ q) (snd G Y)

theorem lift_proj (q : G ⟶ B) {Z : Over S} (g : Z ⟶ G) (y : Z ⟶ Y) :
    lift g y ≫ proj q Y = lift (g ≫ q) y := by
  simp [comp_lift]

theorem exists_gen_of_weight (i : splitTorus S X ⟶ G) (q : G ⟶ B)
    [Flat (proj q Y).left] [Surjective (proj q Y).left] [QuasiCompact (proj q Y).left]
    (ker : ∀ {Z : Over S} (g g' : Z ⟶ G), g ≫ q = g' ≫ q → ∃ t : Z ⟶ splitTorus S X, g = (t ≫ i) * g')
    {N : LB (B ⊗ Y).left} (hN : N.IsLB) (u : LB.Gen (N.pull ((proj q Y).left ≫ 𝟙 _))) (hu : u.IsGen)
    (χ : X) (hw : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val u (lift ((t ≫ i) * g) y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * val u (lift g y).left z J)
    (f : Γ(G.left, ⊤)ˣ) (hf : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left),
      gm ((t ≫ i) * g).left z ⊤ f = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z ⊤ f) :
    ∃ t : LB.Gen (N.pull (𝟙 _)), t.IsGen := by
  let v : Γ((G ⊗ Y).left, ⊤)ˣ := (Units.map (fst G Y).left.appTop.hom.toMonoidHom f)⁻¹
  have val' : ∀ (Z : Over S) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val (scaleGen v u) (lift g y).left z J = (gm g.left z ⊤ f)⁻¹ * val u (lift g y).left z J := by
    intro Z g y z J hJ
    rw [val_scaleGen _ _ _ hJ, map_inv, gm_pullTop, ← Over.comp_left, lift_fst]
  have inv : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (y : Z ⟶ Y) (z : Z.left) (J), Good N z J →
      val (scaleGen v u) (lift ((t ≫ i) * g) y).left z J = val (scaleGen v u) (lift g y).left z J := by
    intro Z t g y z J hJ
    rw [val' _ _ _ z J hJ, val' _ _ _ z J hJ, hf, hw _ _ _ _ z J hJ, mul_inv,
      _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
  obtain ⟨t, ht, -⟩ := exists_gen_descend_val hN (proj q Y).left (fun _ : PUnit => 𝟙 _) (fun _ => 1)
    (scaleGen v u) (scaleGen_isGen _ hu) fun Z g₁ g₂ z J hJ e => by
      let T : Over S := Over.mk (g₂ ≫ (G ⊗ Y).hom)
      let k₂ : T ⟶ G ⊗ Y := Over.homMk g₂ rfl
      let k₁ : T ⟶ G ⊗ Y := Over.homMk g₁ (by
        change g₁ ≫ (G ⊗ Y).hom = g₂ ≫ (G ⊗ Y).hom
        rw [← Over.w (proj q Y), reassoc_of% e])
      have e' : k₁ ≫ proj q Y = k₂ ≫ proj q Y := Over.OverMorphism.ext e
      have h₁ : k₁ = lift (k₁ ≫ fst _ _) (k₁ ≫ snd _ _) := by ext <;> simp
      have h₂ : k₂ = lift (k₂ ≫ fst _ _) (k₂ ≫ snd _ _) := by ext <;> simp
      have ex : (k₁ ≫ fst _ _) ≫ q = (k₂ ≫ fst _ _) ≫ q := by
        simpa using e' =≫ fst _ _
      have ey : k₁ ≫ snd G Y = k₂ ≫ snd G Y := by
        simpa using e' =≫ snd _ _
      obtain ⟨t, ht⟩ := ker _ _ ex
      have a₁ : g₁ = (lift ((t ≫ i) * (k₂ ≫ fst _ _)) (k₂ ≫ snd G Y)).left := by
        rw [← ht, ← ey, ← h₁]; rfl
      have a₂ : g₂ = (lift (k₂ ≫ fst _ _) (k₂ ≫ snd G Y)).left := by
        rw [← h₂]; rfl
      rw [a₁, a₂]
      exact inv T t _ _ z J hJ
  exact ⟨t, ht⟩

end Main

theorem pic_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (T : TorusExtension G) (Y : Over (Sp k)), Smooth Y.hom → GeometricallyConnected Y.hom → ∀ (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Pic (T.B ⊗ Y).left), pull (lift (fst G Y ≫ T.q) (snd G Y)).left c = 0 → pull (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left c = 0 → c = 0 := by
  intro k _ _ G _ _ hG T Y hYs hYc y₀ c h₁ h₂
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := hG.smooth
  have := hG.geomConnected
  have hsm : Smooth (G ⊗ Y).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ Y).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    exact GeometricallyConnected.comp _ _
  have : ConnectedSpace (G ⊗ Y).left :=
    GeometricallyConnected.connectedSpace (G ⊗ Y).hom (G ⊗ Y).hom.isOpenMap
  have : IsReduced (G ⊗ Y).left := isReduced_of_smooth (G ⊗ Y).hom
  have eπ : proj T.q Y = T.q ⊗ₘ 𝟙 Y := by ext <;> simp
  have hid₁ : Flat (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have hid₂ : Surjective (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have hid₃ : QuasiCompact (𝟙 Y : Y ⟶ Y).left := by rw [Over.id_left]; infer_instance
  have : Flat (proj T.q Y).left := eπ ▸ CosetQuotient.flat_tensorHom T.q (𝟙 Y)
  have : Surjective (proj T.q Y).left := eπ ▸ CosetQuotient.surjective_tensorHom T.q (𝟙 Y)
  have : QuasiCompact (proj T.q Y).left := eπ ▸ CosetQuotient.quasiCompact_tensorHom T.q (𝟙 Y)
  have hiq : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) T.X) (g : Z ⟶ G), ((t ≫ T.i) * g) ≫ T.q = g ≫ T.q := by
    intro Z t g
    rw [MonObj.mul_comp, Category.assoc, T.isKernel.w, ← Category.assoc,
      toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
  have ker : ∀ {Z : Over (Sp k)} (g g' : Z ⟶ G), g ≫ T.q = g' ≫ T.q →
      ∃ t : Z ⟶ splitTorus (Sp k) T.X, g = (t ≫ T.i) * g' := by
    intro Z g g' e
    have h : (g * g'⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
      rfl
    exact ⟨T.isKernel.lift _ _ h, by rw [T.isKernel.lift_fst, inv_mul_cancel_right]⟩
  obtain ⟨u, hu⟩ := (cls_eq_zero_iff (pull_isLB hN ((proj T.q Y).left ≫ 𝟙 _))).1 (by
    rw [cls_pull hN, Category.comp_id]; exact h₁)
  obtain ⟨s, hs⟩ := (cls_eq_zero_iff (pull_isLB hN (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left)).1 (by
    rw [cls_pull hN]; exact h₂)
  obtain ⟨χ, hw⟩ := exists_weight T.i ((proj T.q Y).left ≫ 𝟙 _) (by
    rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left]
    congr 1
    have e₁ : snd (splitTorus (Sp k) T.X) (G ⊗ Y) ≫ proj T.q Y =
        lift ((snd _ _ ≫ fst G Y) ≫ T.q) (snd _ _ ≫ snd G Y) := by
      rw [proj, comp_lift, Category.assoc]
    rw [act, lift_proj, e₁, hiq]) hN u hu
  obtain ⟨f, hf⟩ := exists_unit_weight T.i T.q hiq ((proj T.q Y).left ≫ 𝟙 _)
    (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left y₀ (by
      rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left, sec, lift_proj]
      simp [comp_lift, toUnit_unique (T.q ≫ toUnit T.B) (toUnit G)]) hN u hu s hs χ hw
  obtain ⟨t, ht⟩ := exists_gen_of_weight T.i T.q ker hN u hu χ hw f hf
  have h := (cls_eq_zero_iff (pull_isLB hN (𝟙 _))).2 ⟨t, ht⟩
  rwa [cls_pull hN, pull_id] at h

end GlobalTheory.CompanionTheory.TorusPic

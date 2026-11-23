import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

def QkPullExistsSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : Out.DegPre R)
    (D' : Out.DegPre R') (hD : Out.IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F],
    (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) →
    ∀ (k : ℕ) (p' : Out.QkPt D' F k), ∃ p : Out.QkPt D F k, p'.y = hD.xe.symm p.y ∧ Out.IsPullGtF φ hD F p.g p'.g

def PolOActPullSt : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : Out.PolAV S) (P' : Out.PolAV S') (g : P'.A.left ⟶ P.A.left),
    IsGrpPullback P'.A P.A f g → LBIso (P.L.pull g) P'.L →
    ∀ (O : Type) [CommRing O] [StarRing O] (o : P.OAct O), ∃ o' : P'.OAct O,
      ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left

section Grp

variable {S S' : Scheme.{0}}

theorem IsGrpPullback.congr {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f f' : S' ⟶ S} {φ φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (e : f = f') (e' : φ = φ') : IsGrpPullback G' G f' φ' := by
  subst e e'
  exact h

theorem isGrpPullback_of_iso {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ≅ G₂) [IsMonHom e.hom] :
    IsGrpPullback G₁ G₂ (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  rw [← Over.comp_left, MonObj.mul_comp]
  obtain ⟨Tl, ⟨⟨⟩⟩, Th⟩ := T
  exact mul_left_congr (Category.comp_id _) x₀ y₀ (x ≫ e.hom) (y ≫ e.hom) hx hy

theorem grpPullback_iso {G : Over S} {G₁ G₂ : Over S'} [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S' ⟶ S}
    {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f φ₁) (h₂ : IsGrpPullback G₂ G f φ₂) :
    ∃ e : G₁ ≅ G₂, IsMonHom e.hom ∧ e.hom.left ≫ φ₂ = φ₁ := by
  let e : G₁ ≅ G₂ := Over.isoMk (h₁.1.isoIsPullback _ _ h₂.1) (h₁.1.isoIsPullback_hom_snd _ _ h₂.1)
  have he : e.hom.left ≫ φ₂ = φ₁ := h₁.1.isoIsPullback_hom_fst _ _ h₂.1
  have mul : ∀ (T : Over S') (x y : T ⟶ G₁), (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
    intro T x y
    apply Over.OverMorphism.ext
    apply h₂.1.hom_ext
    · rw [Over.comp_left, Category.assoc, he, ← h₁.2 T x y (pushPt h₁.1.w x) (pushPt h₁.1.w y) rfl rfl]
      exact h₂.2 T _ _ _ _ (by show x.left ≫ φ₁ = (x.left ≫ _) ≫ φ₂; rw [Category.assoc, he])
        (by show y.left ≫ φ₁ = (y.left ≫ _) ≫ φ₂; rw [Category.assoc, he])
    · rw [Over.w, Over.w]
  refine ⟨e, ⟨?_, ?_⟩, he⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G₁) ≫ e.hom = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

end Grp

section Iso

variable {X Y Y' : Scheme.{0}}

def chartPullSame (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k = h ≫ φ k) : ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun j y hy => Set.mem_iInter.2 fun k => by
    have : φ' k y ∈ L.U (j k) := Set.mem_iInter.1 hy k
    rw [hc] at this; exact this
  { idx := fun j => j
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans (Finset.prod_congr rfl fun k _ => ?_)
        (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      rw [Category.id_comp, hc] }

def chartPullId (L : LB X) : ChartPull L L (𝟙 X) := ⟨fun i => i, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩

def chartPullUnpull (L : LB X) (F : X ⟶ X) (e : F = 𝟙 X) : ChartPull L (L.pull F) (𝟙 X) where
  idx i := fun _ => i
  le i y hy := by subst e; exact mem_pull.2 hy
  g y i j hi hj := by
    subst e
    exact ((gm_pull_g L (𝟙 X) (𝟙 X) y (fun _ => i) (fun _ => j) (mem_pull.2 hi) (mem_pull.2 hj)).trans
      (by rw [Category.id_comp])).symm

private lemma res_res_toroidal_compactification {A : Scheme.{0}} {U V W : A.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(A, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  ext1
  have e := congrArg (fun g => g.hom (u : Γ(A, U))) (A.presheaf.map_comp (homOfLE h2).op (homOfLE h1).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [res, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact e.symm

theorem pull_isLB {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB where
  cover := top_le_iff.1 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart hL (F y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  g_self J := unit_ext fun y hy => by
    rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
    exact gm_self hL _ y (mem_pull.1 hy)
  cocycle I J K := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
      gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
    exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)

private lemma res_mul_inv_mul_of_eq {A : Scheme.{0}} {U V : A.Opens} (h : V ≤ U) (x y z w : Γ(A, U)ˣ)
    (hx : x = y * z⁻¹ * w) : res h x = res h y * (res h z)⁻¹ * res h w := by
  rw [hx, map_mul, map_mul, map_inv]

private lemma inv_eq_mul_inv_mul_inv_of_eq_mul_inv_mul {G : Type*} [CommGroup G] (x a b y : G) (h : x = a * b⁻¹ * y) :
    x⁻¹ = b * a⁻¹ * y⁻¹ := by
  rw [h]
  simp only [mul_inv_rev, inv_inv]
  exact mul_comm _ _

theorem LBIso.symm {A B : LB X} (H : LBIso A B) : LBIso B A := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun p => (res (le_inf inf_le_right inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1)
    (w.s (p.2, p.1)))⁻¹⟩, fun p q => ?_⟩
  have hc : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) :=
    le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))
      (le_inf (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left))
  have hg := hw (p.2, p.1) (q.2, q.1)
  have e := res_mul_inv_mul_of_eq hc _ _ _ _ hg
  have e2 := inv_eq_mul_inv_mul_inv_of_eq_mul_inv_mul _ _ _ _ e
  show res (inf_le_left : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ A.U p.1 ⊓ B.U p.2)
      (res (le_inf inf_le_right inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ =
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ A.U p.1 ⊓ A.U q.1)
        (A.g p.1 q.1) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ B.U p.2 ⊓ B.U q.2)
        (B.g p.2 q.2))⁻¹ *
      res (inf_le_right : (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ≤ A.U q.1 ⊓ B.U q.2)
        (res (le_inf inf_le_right inf_le_left : A.U q.1 ⊓ B.U q.2 ≤ B.U q.2 ⊓ A.U q.1) (w.s (q.2, q.1)))⁻¹
  rw [map_inv, map_inv]
  refine (congrArg Inv.inv ((res_res_toroidal_compactification _ _ _).trans (res_res_toroidal_compactification _ _ _).symm)).trans (e2.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (res_res_toroidal_compactification _ _ _) (congrArg Inv.inv (res_res_toroidal_compactification _ _ _))) ?_
  exact congrArg Inv.inv ((res_res_toroidal_compactification _ _ _).trans (res_res_toroidal_compactification _ _ _).symm)

theorem LBIso.trans {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w', h'⟩ := H.chartPull (chartPullId A) (chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w, h⟩ := H'.chartPull (chartPullId B) (chartPullPull C (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w'', T⟩ := exists_comp hB w w' ((isGen_iff w).1 h) ((isGen_iff w').1 h') hC hA
  exact LBIso.chartPull (chartPullId A) (chartPullUnpull C _ (Category.id_comp _))
    ⟨w'', (isGen_iff w'').2 (T.pgen_comp hB ((isGen_iff w).1 h) ((isGen_iff w').1 h'))⟩

private lemma germ_app_presheaf_map_eq_germ_app {A B : Scheme.{0}} (f : A ⟶ B) (y : A) {U V : B.Opens} (hVU : V ≤ U)
    (hy : f y ∈ V) (a : Γ(B, U)) :
    (A.presheaf.germ (f ⁻¹ᵁ V) y hy).hom ((f.app V).hom ((B.presheaf.map (homOfLE hVU).op).hom a)) =
      (A.presheaf.germ (f ⁻¹ᵁ U) y (hVU hy)).hom ((f.app U).hom a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.Hom.naturality f (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat
  rw [nat]
  first
    | exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    | exact TopCat.Presheaf.germ_res_apply _ _ _ _ _ _
    | (erw [TopCat.Presheaf.germ_res_apply])
    | (simp; done)

private lemma germ_app_app_eq_germ_app_comp {A B C : Scheme.{0}} (r : A ⟶ B) (h : B ⟶ C) (y : A) (W : C.Opens)
    (hy : h (r y) ∈ W) (a : Γ(C, W)) :
    (A.presheaf.germ (r ⁻¹ᵁ h ⁻¹ᵁ W) y hy).hom ((r.app (h ⁻¹ᵁ W)).hom ((h.app W).hom a)) =
      (A.presheaf.germ ((r ≫ h) ⁻¹ᵁ W) y hy).hom (((r ≫ h).app W).hom a) := by
  first
    | rfl
    | (simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; rfl)
    | (simp [Scheme.Hom.comp_app]; done)

private lemma gm_res_toroidal_compactification {A B : Scheme.{0}} (f : A ⟶ B) (y : A) {U V : B.Opens} (hVU : V ≤ U)
    (hy : f y ∈ V) (u : Γ(B, U)ˣ) : gm f y V (res hVU u) = gm f y U u := by
  ext1
  rw [gm, gm, dif_pos hy, dif_pos (hVU hy)]
  simp only [MonoidHom.comp_apply, Units.coe_map, res, pullU, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact germ_app_presheaf_map_eq_germ_app f y hVU hy _

theorem gm_corr {Z : Scheme.{0}} (L : LB X) {φ φ' : PUnit → (Y ⟶ X)} {ε ε' : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (h : LB.Gen.Corr L φ ε φ' ε' t t') (r : Z ⟶ Y) (z : Z) (j : L.ι)
    (h₁ : r z ∈ LB.wchart L φ (fun _ => j)) (h₂ : r z ∈ LB.wchart L φ' (fun _ => j)) :
    gm r z (LB.wchart L φ (fun _ => j)) (t.s (fun _ => j)) = gm r z (LB.wchart L φ' (fun _ => j)) (t'.s (fun _ => j)) := by
  have hC : ∀ (ψ : PUnit → (Y ⟶ X)) (j' : PUnit → L.ι), LB.Coh L ψ j' := fun _ j' k₁ k₂ _ => by
    cases k₁; cases k₂; rfl
  have hc := h (fun _ => j) (fun _ => j) (hC _ _) (hC _ _) (fun _ _ _ => rfl)
  have hW : r z ∈ LB.wchart L φ (fun _ => j) ⊓ LB.wchart L φ' (fun _ => j) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨h₁, h₂⟩
  exact ((gm_res_toroidal_compactification r z inf_le_left hW _).symm.trans (congrArg (gm r z _) hc)).trans
    (gm_res_toroidal_compactification r z inf_le_right hW _)

theorem gm_pullGen {Z Z' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (r : Z' ⟶ Z) (z : Z') (j : K → L.ι)
    (hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) j) :
    gm r z (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by
  have hz' : h (r z) ∈ LB.wchart L φ j := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
  have hle : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  ext1
  rw [gm, gm, dif_pos hz, dif_pos (show (r ≫ h) z ∈ LB.wchart L φ j from hz')]
  simp only [LB.pullGen, MonoidHom.comp_apply, Units.coe_map, res, pullU, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  exact (germ_app_presheaf_map_eq_germ_app r z hle hz _).trans (germ_app_app_eq_germ_app_comp r h z _ hz' _)

end Iso

section Field

variable {F : Type} [Field F] {X : Scheme.{0}}

def toStk (z : Sp F) : F →+* (Sp F).presheaf.stalk z :=
  ((Sp F).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem top_le_iff_mem (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by
  constructor
  · intro hle
    exact hle (show z ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro hz w _
    have hwz : w = z := by
      first
        | exact Subsingleton.elim _ _
        | exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
        | exact PrimeSpectrum.ext (by simp)
    subst hwz
    exact hz

theorem toStk_valF (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) (a : Γ(X, U)ˣ) :
    toStk z (valF x U a.val) = (gm x z U a).val := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := (top_le_iff_mem x U z).2 h
  have e1 := congrArg (fun g => g.hom ((x.appLE U ⊤ h').hom a.val))
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at e1
  rw [valF, dif_pos h', gm, dif_pos h]
  simp only [toStk, RingHom.comp_apply, MonoidHom.comp_apply, Units.coe_map, pullU,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [e1]
  first
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       exact TopCat.Presheaf.germ_res_apply _ _ _ _ _)
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       erw [TopCat.Presheaf.germ_res_apply])
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans rfl)
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       exact Eq.refl _)

variable {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}

theorem genRel_iff {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) (z : Sp F) :
    GenRel w t t₀ x ↔ (∀ k, pt k ≫ φ = pt₀ k) ∧ ∀ (j : K → M.ι) (j₀ : K → M₀.ι), (∀ k, φ (pt k z) ∈ M₀.U (j₀ k)) →
      (∀ k, pt k z ∈ M.U (j k)) →
      ((∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val := by
  refine and_congr_right fun hp => forall_congr' fun j => forall_congr' fun j₀ => ?_
  have key : (∀ k, φ (pt k z) ∈ M₀.U (j₀ k)) → (∀ k, pt k z ∈ M.U (j k)) →
      (valF (𝟙 (Sp F)) _ (t.s j).val =
        x * (∏ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ^ (-ε k)) * valF (𝟙 (Sp F)) _ (t₀.s j₀).val ↔
      ((∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val) := by
    intro h₀ h₁
    have a₁ := toStk_valF (𝟙 (Sp F)) (LB.wchart M pt j) z (Set.mem_iInter.2 h₁) (t.s j)
    have a₂ := toStk_valF (𝟙 (Sp F)) (LB.wchart M₀ pt₀ j₀) z (Set.mem_iInter.2 fun k => by
      have := h₀ k
      rw [← hp k]; exact this) (t₀.s j₀)
    have a₃ : ∀ k, toStk z (valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val) = (gw w (pt k) z (j₀ k) (j k)).val := fun k =>
      toStk_valF (pt k) ((M₀.pull φ).U (fun _ => j₀ k) ⊓ M.U (j k)) z ⟨mem_pull.2 (h₀ k), h₁ k⟩ _
    have a₄ : toStk z (∏ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ^ (-ε k)) =
        ((∏ k, gw w (pt k) z (j₀ k) (j k) ^ ε k)⁻¹).val := by
      have hu : ∀ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ≠ 0 := fun k h0 => by
        have := a₃ k
        rw [h0, map_zero] at this
        exact (gw w (pt k) z (j₀ k) (j k)).ne_zero this.symm
      rw [map_prod, ← Finset.prod_inv_distrib, Units.coe_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      have e : Units.map (toStk z).toMonoidHom (Units.mk0 _ (hu k)) = gw w (pt k) z (j₀ k) (j k) := Units.ext (a₃ k)
      rw [← e, ← zpow_neg, ← map_zpow]
      show _ = toStk z _
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← (toStk z).injective.eq_iff, map_mul, map_mul, a₄]
    refine Iff.trans (Eq.congr a₁ (congrArg _ a₂)) ?_
    rw [Units.val_mul, mul_comm (toStk z x), _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
  constructor
  · intro H h₀ h₁
    exact (key h₀ h₁).1 (H fun k => (top_le_iff_mem _ _ z).2 ⟨mem_pull.2 (h₀ k), h₁ k⟩)
  · intro H h
    have h₀ := fun k => mem_pull.1 ((top_le_iff_mem _ _ z).1 (h k)).1
    have h₁ := fun k => ((top_le_iff_mem _ _ z).1 (h k)).2
    exact (key h₀ h₁).2 (H h₀ h₁)

theorem genRel_transfer {φ : B ⟶ B₀} {Φ : B' ⟶ B} {w : LB.Iso M (M₀.pull φ)} {wD : LB.Iso M' (M.pull Φ)}
    {w' : LB.Iso M' (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') (hM : M.IsLB) (hM' : M'.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hc : ∀ k, pt' k ≫ Φ = 𝟙 _ ≫ pt k)
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M' pt' ε)} (H : PMaps wD pt' pt ε t' t (𝟙 _))
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) : GenRel w t t₀ x ↔ GenRel w' t' t₀ x := by
  have z : Sp F := (default : PrimeSpectrum F)
  have hc' : ∀ k, pt' k ≫ Φ = pt k := fun k => (hc k).trans (Category.id_comp _)
  have pe : ∀ k, pt k z = Φ (pt' k z) := fun k => congrArg (fun g => g z) (hc' k).symm
  have key : ∀ (j₀ : K → M₀.ι) (i : K → M.ι) (q : K → M'.ι), (∀ k, φ (Φ (pt' k z)) ∈ M₀.U (j₀ k)) →
      (∀ k, Φ (pt' k z) ∈ M.U (i k)) → (∀ k, pt' k z ∈ M'.U (q k)) →
      (∏ k, gw w' (pt' k) z (j₀ k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M' pt' q) (t'.s q) =
        (∏ k, gw w (pt k) z (j₀ k) (i k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt i) (t.s i) := by
    intro j₀ i q h₀ h₁ h₂
    have a := T.prod (ε := ε) hc _ (𝟙 _) z j₀ i q h₀ h₁ h₂
    have b := H _ (𝟙 _) z i q h₁ h₂
    simp only [Category.id_comp] at a b
    rw [a, b, _root_.mul_assoc]
  rw [genRel_iff w t t₀ x z, genRel_iff w' t' t₀ x z]
  refine and_congr (forall_congr' fun k => by rw [← Category.assoc, hc']) ⟨fun H' q j₀ h₀ h₂ => ?_, fun H' i j₀ h₀ h₁ => ?_⟩
  · choose i hi using fun k => exists_chart hM (Φ (pt' k z))
    rw [key j₀ i q h₀ hi h₂]
    exact H' i j₀ (fun k => by rw [pe]; exact h₀ k) (fun k => by rw [pe]; exact hi k)
  · choose q hq using fun k => exists_chart hM' (pt' k z)
    have h₀' : ∀ k, φ (Φ (pt' k z)) ∈ M₀.U (j₀ k) := fun k => by rw [← pe]; exact h₀ k
    rw [← key j₀ i q h₀' (fun k => by rw [← pe]; exact h₁ k) hq]
    exact H' q j₀ h₀' hq

end Field

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

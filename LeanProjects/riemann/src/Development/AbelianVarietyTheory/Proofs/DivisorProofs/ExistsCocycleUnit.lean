import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TorusModel GlobalTheory.TorusCoordPull

namespace GlobalTheory.FormalModel

theorem exists_cocycle_unit {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {c : X' ⟶ X'} (hc : c ≫ F = F)
    (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} {v : LB.Iso L' (L'.pull c)} (hw : PGen w) (hv : PGen v) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' →
      om w z J J' (q ≫ c) * om v z J' J' q = gm q z ⊤ u * om w z J J' q := by
  let W : L.ι × L'.ι × L'.ι → X'.Opens := fun p => c ⁻¹ᵁ ((L.pull F).U (fun _ => p.1) ⊓ L'.U p.2.1) ⊓
    ((L'.pull c).U (fun _ => p.2.1) ⊓ L'.U p.2.2) ⊓ ((L.pull F).U (fun _ => p.1) ⊓ L'.U p.2.2)
  let u : ∀ p, Γ(X', W p)ˣ := fun p => res (inf_le_left.trans inf_le_left) (pullU c _ (w.s (fun _ => p.1, p.2.1))) *
    res (inf_le_left.trans inf_le_right) (v.s (fun _ => p.2.1, p.2.2)) * (res inf_le_right (w.s (fun _ => p.1, p.2.2)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (q : Z ⟶ X') (z : Z) p, q z ∈ W p →
      gm q z (W p) (u p) = gw w (q ≫ c) z p.1 p.2.1 * gw v q z p.2.1 p.2.2 * (gw w q z p.1 p.2.2)⁻¹ := fun Z q z p h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res q z _ h _).trans (gm_pull q c z _ h.1.1 _)) (gm_res q z _ h _)))
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res q z _ h _))))
  have hF : ∀ x : X', F (c x) = F x := fun x => by rw [← Scheme.Hom.comp_apply, hc]
  have mem : ∀ (x : X') p, F x ∈ L.U p.1 → c x ∈ L'.U p.2.1 → x ∈ L'.U p.2.2 → x ∈ W p := fun x p h₁ h₂ h₃ =>
    ⟨⟨⟨mem_pull.2 (by rw [hF]; exact h₁), h₂⟩, mem_pull.2 h₂, h₃⟩, mem_pull.2 h₁, h₃⟩
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hL (F x)
      obtain ⟨b, hb⟩ := exists_chart hL' (c x)
      obtain ⟨d, hd⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, d), mem x _ ha hb hd⟩) u (fun p p' x hx => by
      rw [hu _ _ x p hx.1, hu _ _ x p' hx.2,
        hw _ (𝟙 _ ≫ c) x p.1 p'.1 p.2.1 p'.2.1 (mem_pull.1 hx.1.1.1.1) (mem_pull.1 hx.2.1.1.1) hx.1.1.1.2 hx.2.1.1.2,
        hv _ (𝟙 _) x p.2.1 p'.2.1 p.2.2 p'.2.2 hx.1.1.1.2 hx.2.1.1.2 hx.1.2.2 hx.2.2.2,
        hw _ (𝟙 _) x p.1 p'.1 p.2.2 p'.2.2 (mem_pull.1 hx.1.2.1) (mem_pull.1 hx.2.2.1) hx.1.2.2 hx.2.2.2,
        Category.assoc, hc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨s, fun Z q z J J' hJ hJ' => ?_⟩
  have m := mem (q z) (J (q ≫ F), J' (q ≫ c), J' q) (hJ (q ≫ F)) (hJ' (q ≫ c)) (hJ' q)
  have e := (gm_res q z le_top m s).symm.trans ((congrArg (gm q z _) (hs _)).trans (hu Z q z _ m))
  rw [e, om, om, om, Category.assoc, hc, inv_mul_cancel_right]

theorem prod_cocycle {X S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B) {L : LB X} {L' : LB B.left}
    {F : B.left ⟶ X} {c : B.left ⟶ B.left} (hc : c ≫ F = F) (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)}
    {v : LB.Iso L' (L'.pull c)} (hw : PGen w) (hv : PGen v) {Z : Scheme.{0}} (q q' : Fin 4 → (Z ⟶ B.left))
    (hq : ∀ k, q k ≫ B.hom = q 2 ≫ B.hom) (hq' : ∀ k, q k ≫ c = q' k) {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : (∏ k, om w z J J' (q' k) ^ Oinvε k) * ∏ k, om v z J' J' (q k) ^ Oinvε k =
      ∏ k, om w z J J' (q k) ^ Oinvε k := by
  obtain ⟨u, hu⟩ := exists_cocycle_unit hc hL hL' hw hv
  obtain ⟨u₀, hu₀⟩ := (globalFns_holds _ _ hB).2 u.val
  have cst : ∀ k, gm (q k) z ⊤ u = gm (q 2) z ⊤ u := fun k => by
    refine Units.ext ?_
    rw [← gs_unit (q k) z ⊤ trivial, ← gs_unit (q 2) z ⊤ trivial, ← hu₀]
    exact (gs_pull _ B.hom z ⊤ trivial u₀).trans ((congrArg (fun q => gs q z ⊤ u₀) (hq k)).trans
      (gs_pull _ B.hom z ⊤ trivial u₀).symm)
  have key : ∀ k, om w z J J' (q' k) * om v z J' J' (q k) = gm (q 2) z ⊤ u * om w z J J' (q k) := fun k => by
    rw [← hq' k, ← cst k]
    exact hu _ _ z J J' hJ hJ'
  rw [← Finset.prod_mul_distrib]
  simp only [← mul_zpow, key]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  refine mul_eq_right.2 ?_
  rw [Fin.prod_univ_four]
  show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) = 1
  simp

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg ρ D D')

theorem exists_gtPt_up {T' : Over (Sp R')} (g' : GtPt D' T') : ∃ g : GtPt D (Over.mk (T'.hom ≫ spMap ρ)),
    g.b.left = g'.b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) ∧
    ∀ y (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (g.s (hD.xe y)) r z J =
        (∏ k, om hD.w z J J' (r ≫ DegPre.gtφT D' T' g'.b y k) ^ DegPre.gtε k) * val (g'.s y) r z J' := by
  have gp := pull_grp hD
  have hw := (isGen_iff hD.w).1 hD.w_gen
  let b := pushPt gp.1.w g'.b
  have hψ : ∀ χ k, DegPre.gtφT D' T' g'.b (hD.xe.symm χ) k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) =
      𝟙 _ ≫ DegPre.gtφT D _ b χ k := fun χ k => by
    rw [TorusCoord.gtφT_eq, TorusCoord.gtφT_eq]
    have := Oφ_pull hD b g'.b (𝟙 _) (Category.id_comp _).symm (hD.xe.symm χ) k
    rwa [AddEquiv.apply_symm_apply] at this
  have ex : ∀ χ, ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D _ b χ) DegPre.gtε), t.IsGen ∧
      PMaps hD.w (DegPre.gtφT D' T' g'.b (hD.xe.symm χ)) (DegPre.gtφT D _ b χ) DegPre.gtε (g'.s _) t (𝟙 _) := fun χ => by
    have e : DegPre.gtφT D _ b χ = fun k => DegPre.gtφT D' T' g'.b (hD.xe.symm χ) k ≫
      hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) := funext fun k => ((hψ χ k).trans (Category.id_comp _)).symm
    rw [e]
    obtain ⟨t, ht, h⟩ := exists_up hw D.P.isLB D'.P.isLB (g'.s (hD.xe.symm χ)) (g'.isGen _)
    refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
    exact (congrArg (fun r => gm r z _ _) (Category.comp_id r)).trans (h Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq))
  choose t ht H using ex
  have vt : ∀ y (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (t (hD.xe y)) r z J =
        (∏ k, om hD.w z J J' (r ≫ DegPre.gtφT D' T' g'.b y k) ^ DegPre.gtε k) * val (g'.s y) r z J' := by
    intro y Z r z J J' hJ hJ'
    have := val_of_pmaps (hψ _) (H (hD.xe y)) r hJ hJ'
    rw [AddEquiv.symm_apply_apply] at this
    exact (congrArg (fun r => val (t (hD.xe y)) r z J) (Category.comp_id r)).symm.trans this
  have vt' : ∀ y (z : T'.left) J J', Good D.P.L z J → Good D'.P.L z J' → val (t (hD.xe y)) (𝟙 T'.left) z J =
      (ConstFam.wVal hD.w z J J' (cP D' T' y * g'.b).left)⁻¹ * ConstFam.wVal hD.w z J J' (cP D' T' y).left *
        ConstFam.wVal hD.w z J J' g'.b.left * (ConstFam.wVal hD.w z J J' (1 : T' ⟶ D'.P.A).left)⁻¹ *
        cv g' y z J' := fun y z J J' hJ hJ' => by
    have v := vt y _ (𝟙 _) z J J' hJ hJ'
    have p := FormalPoint.prod_gtφT (𝟙 T') g'.b y (ConstFam.wVal hD.w z J J')
    rw [Category.id_comp] at p
    exact v.trans (congrArg (· * _) p)
  obtain ⟨g, hg, hv⟩ := exists_pt b t ht (fun χ _ _ _ => rfl) (fun z J hJ => by
      obtain ⟨J', hJ'⟩ := exists_good' D'.P.isLB z
      have v := vt' 0 z J J' hJ hJ'
      rw [map_zero, cv_zero g' hJ', cPoint_zero, _root_.one_mul] at v
      refine v.trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel) (fun χ χ' z J hJ => by
      obtain ⟨y, rfl⟩ := hD.xe.surjective χ
      obtain ⟨y', rfl⟩ := hD.xe.surjective χ'
      obtain ⟨J', hJ'⟩ := exists_good' D'.P.isLB z
      have c := ConstPoint.th_pushPt globalFns_holds gp hw (T' := T') hJ hJ' (cP D' T' y) (cP D' T' y') g'.b
      rw [push_cP, push_cP] at c
      have v₁ := vt' y z J J' hJ hJ'
      have v₂ := vt' y' z J J' hJ hJ'
      have v₃ := vt' (y + y') z J J' hJ hJ'
      rw [cPoint_add, map_add] at v₃
      have e := cv_add g' hJ' y y'
      refine (congrArg₂ (fun a b : (T'.left.presheaf.stalk z)ˣ => a * b) v₃ c).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) v₁ v₂).symm)
      apply Additive.ofMul.injective
      have a₁ := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at a₁ ⊢
      linear_combination (norm := abel) a₁)
  exact ⟨g, congrArg (·.left) hg, fun y Z r z J J' hJ hJ' => (hv _ Z r z J hJ).trans (vt y Z r z J J' hJ hJ')⟩

section Model

variable {I : Ideal R'} {E : DegData R' I} {hE : IsPullDeg ρ D E.toPre} {A' : PolAV (Sp (FractionRing R'))}
  {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {Y : Over (Sp R)} [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T}

theorem hom_ext (hΦ : Represents Φ) {Z : Scheme.{0}} {r r' : Z ⟶ Y.left}
    (hb : r ≫ (Φ Y (𝟙 Y)).b.left = r' ≫ (Φ Y (𝟙 Y)).b.left)
    (hv : ∀ χ z J, Good D.P.L z J → val ((Φ Y (𝟙 Y)).s χ) r z J = val ((Φ Y (𝟙 Y)).s χ) r' z J) : r = r' := by
  have w : r' ≫ Y.hom = r ≫ Y.hom := by rw [← Over.w (Φ Y (𝟙 Y)).b, ← Category.assoc, ← hb, Category.assoc]
  let k : Over.mk (r ≫ Y.hom) ⟶ Y := Over.homMk r rfl
  let k' : Over.mk (r ≫ Y.hom) ⟶ Y := Over.homMk r' w
  have h₁ := hΦ.1 _ _ k (𝟙 Y)
  have h₂ := hΦ.1 _ _ k' (𝟙 Y)
  rw [Category.comp_id, isPull_iff] at h₁ h₂
  exact congrArg (·.left) ((Φ _).injective (pt_ext (h₁.1.trans ((Over.OverMorphism.ext hb).trans h₂.1.symm))
    fun χ z J hJ => (h₁.2 χ z J hJ).trans ((hv χ z J hJ).trans (h₂.2 χ z J hJ).symm)) : k = k')

variable (hE) in

def Carries {e : ℕ} (c : GtCoord I E.toPre e G') (g : GtPt D Y) (φ : (thickObj R' I e G').left ⟶ Y.left) : Prop :=
  c.pG.left ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) = φ ≫ g.b.left ∧
    ∀ y (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I e G').left) (z : Z) J J', Good D.P.L z J → Good E.toPre.P.L z J' →
      val (g.s (hE.xe y)) (r ≫ φ) z J =
        (∏ k, om hE.w z J J' (r ≫ E.toPre.Oφ c.pG y k) ^ Oinvε k) * val (c.t y) r z J'

variable (hE) in
theorem exists_carries (hΦ : Represents Φ) {e : ℕ} (c : GtCoord I E.toPre e G') :
    ∃ φ, Carries hE c (Φ Y (𝟙 Y)) φ := by
  obtain ⟨ξ, hξ⟩ := TorusCoord.exists_isPointOf c (T := (Over.map (thick R' I e)).obj (thickObj R' I e G')) (𝟙 _)
    (Category.id_comp _)
  obtain ⟨g, hb, hv⟩ := exists_gtPt_up hE ξ
  have hp : ξ.b = c.pG := Over.OverMorphism.ext (hξ.1.trans (Category.id_comp _))
  have h := hΦ.1 _ _ ((Φ _).symm g) (𝟙 Y)
  rw [Category.comp_id, Equiv.apply_symm_apply] at h
  refine ⟨((Φ _).symm g).left, by rw [← hp]; exact hb.symm.trans h.1, fun y Z r z J J' hJ hJ' => ?_⟩
  refine ((val_corr hJ (h.2 _) r).trans (val_pull hJ _ _ _)).symm.trans ((hv y Z r z J J' hJ hJ').trans
    (congrArg₂ (· * ·) (by rw [TorusCoord.gtφT_eq, hp]; rfl) ?_))
  exact (val_corr hJ' (hξ.2 y) r).trans ((val_pull hJ' _ _ _).trans (by rw [Category.comp_id]))

omit [GrpObj Y] in
theorem Carries.w {e : ℕ} {c : GtCoord I E.toPre e G'} {g : GtPt D Y} {φ} (h : Carries hE c g φ) :
    φ ≫ Y.hom = (thickObj R' I e G').hom ≫ thick R' I e ≫ spMap ρ :=
  (over_base hE g.b c.pG φ h.1).trans (Category.assoc _ _ _)

omit [GrpObj Y] in
theorem Carries.ext {e : ℕ} {c : GtCoord I E.toPre e G'} {g : GtPt D Y} {φ} (h : Carries hE c g φ) {Z : Scheme.{0}}
    {y y' : Z ⟶ (thickObj R' I e G').left} (h₁ : y ≫ φ = y' ≫ φ)
    (h₂ : y ≫ (thickObj R' I e G').hom = y' ≫ (thickObj R' I e G').hom) : y = y' := by
  have pw : c.pG.left ≫ E.toPre.P.A.hom = (thickObj R' I e G').hom ≫ thick R' I e := Over.w c.pG
  have hp : y ≫ c.pG.left = y' ≫ c.pG.left := (pull_grp hE).1.hom_ext
    (by rw [Category.assoc, Category.assoc, h.1, reassoc_of% h₁]) (by rw [Category.assoc, Category.assoc, pw, reassoc_of% h₂])
  refine TorusCoord.ext_of_val c y y' hp fun χ z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have a := h.2 χ Z y z J J' hJ hJ'
  have b := h.2 χ Z y' z J J' hJ hJ'
  have o := (TorusCoord.comp_eq_of_left c.pG c.pG y y' hp).1 χ
  rw [TorusCoord.gtφT_eq] at o
  rw [h₁, b] at a
  simp only [o] at a
  exact (mul_left_cancel a).symm

theorem Carries.exists_lift (hΦ : Represents Φ) (U : UnifPre I E A' G') {e : ℕ} {φ}
    (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) {Z : Scheme.{0}} (r : Z ⟶ Y.left) (s : Z ⟶ Sp (R' ⧸ I ^ (e + 1)))
    (w : r ≫ Y.hom = s ≫ thick R' I e ≫ spMap ρ) : ∃ y, y ≫ φ = r ∧ y ≫ (thickObj R' I e G').hom = s := by
  have := mono_thick I e
  have pw : (U.gt e).pG.left ≫ E.toPre.P.A.hom = (thickObj R' I e G').hom ≫ thick R' I e := Over.w (U.gt e).pG
  obtain ⟨g', hg'⟩ := ConstPoint.exists_gtPt_through globalFns_holds (pull_grp hE) hE.w_gen hE.xe.toAddMonoidHom hE.c_pr
    (T' := Over.mk (s ≫ thick R' I e)) r (w.trans (Category.assoc _ _ _).symm) (Φ Y (𝟙 Y))
  obtain ⟨y, hy⟩ := FormalPoint.exists_hasCoords U e g' (𝟙 _) s (Category.id_comp _).symm
  rw [FormalPoint.hasCoords_iff] at hy
  refine ⟨y, hom_ext hΦ ?_ fun χ z J hJ => ?_, ?_⟩
  · rw [Category.assoc, ← h.1, reassoc_of% hy.1]
    exact (hg' 0).1 2
  · obtain ⟨χ, rfl⟩ := hE.xe.surjective χ
    obtain ⟨J', hJ'⟩ := exists_good' E.toPre.P.isLB z
    have a := (hg' χ).2 Z (𝟙 _) z J J' hJ hJ'
    have o := (TorusCoord.comp_eq_of_left g'.b (U.gt e).pG (𝟙 _) y hy.1.symm).1 χ
    refine (h.2 χ Z y z J J' hJ hJ').trans (Eq.trans ?_ (a.symm.trans
      (congrArg (fun r => val ((Φ Y (𝟙 Y)).s (hE.xe χ)) r z J) (Category.id_comp r))))
    exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (fun q => om hE.w z J J' q ^ Oinvε k) (o k).symm)
      (hy.2 χ z J' hJ')
  · rw [← cancel_mono (thick R' I e), Category.assoc, ← pw, reassoc_of% hy.1]
    exact Over.w g'.b

theorem Carries.isPullback (hΦ : Represents Φ) (U : UnifPre I E A' G') {e : ℕ} {φ}
    (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) :
    IsPullback φ (thickObj R' I e G').hom Y.hom (thick R' I e ≫ spMap ρ) := by
  choose l h₁ h₂ using fun s : PullbackCone Y.hom (thick R' I e ≫ spMap ρ) =>
    h.exists_lift hΦ U s.fst s.snd s.condition
  exact ⟨⟨h.w⟩, ⟨PullbackCone.IsLimit.mk _ l h₁ h₂ fun s m a b => h.ext (a.trans (h₁ s).symm) (b.trans (h₂ s).symm)⟩⟩

theorem Carries.succ (hΦ : Represents Φ) (U : UnifPre I E A' G') {e : ℕ} {φ φ'}
    (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) (h' : Carries hE (U.gt (e + 1)) (Φ Y (𝟙 Y)) φ') :
    thickMap R' I e G' ≫ φ' = φ := by
  refine hom_ext hΦ (by rw [Category.assoc, ← h'.1, ← h.1, reassoc_of% U.gt_q e]) fun χ z J hJ => ?_
  obtain ⟨χ, rfl⟩ := hE.xe.surjective χ
  obtain ⟨J', hJ'⟩ := exists_good' E.toPre.P.isLB z
  have a := h.2 χ _ (𝟙 _) z J J' hJ hJ'
  have o := (TorusCoord.comp_eq_of_left (U.gt (e + 1)).pG (U.gt e).pG (thickMap R' I e G') (𝟙 _)
    ((U.gt_q e).trans (Category.id_comp _).symm)).1 χ
  rw [TorusCoord.gtφT_eq] at o
  refine (h'.2 χ _ _ z J J' hJ hJ').trans (Eq.trans ?_ (a.symm.trans
    (congrArg (fun r => val ((Φ Y (𝟙 Y)).s (hE.xe χ)) r z J) (Category.id_comp φ))))
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (fun q => om hE.w z J J' q ^ Oinvε k) (o k)) ?_
  exact ((val_pull hJ' _ _ _).trans (by rw [Category.id_comp])).symm.trans (val_corr hJ' (U.gt_t e χ) (𝟙 _))

theorem Carries.invariant (hΦ : Represents Φ) {e : ℕ} {c : GtCoord I E.toPre e G'} {φ}
    (h : Carries hE c (Φ Y (𝟙 Y)) φ) {s : R' →+* R'} (p : IsPullDeg s E.toPre E.toPre) (hp : PullOver hE p)
    {m : (thickObj R' I e G').left ⟶ (thickObj R' I e G').left}
    (hm : c.pG.left ≫ p.e.hom.left ≫ pullback.fst E.toPre.P.A.hom (specOf s) = m ≫ c.pG.left)
    (ht : ∀ x, PMaps p.w (E.toPre.Oφ c.pG x) (E.toPre.Oφ c.pG (p.xe x)) Oinvε (c.t x) (c.t (p.xe x)) m) :
    m ≫ φ = φ := by
  have hc := hp.2 _ _ rfl rfl
  refine hom_ext hΦ (by rw [Category.assoc, ← h.1, ← reassoc_of% hm]; exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans hc))
    fun χ z J hJ => ?_
  obtain ⟨χ, rfl⟩ := hE.xe.surjective χ
  obtain ⟨J', hJ'⟩ := exists_good' E.toPre.P.isLB z
  have o := Oφ_pull p c.pG c.pG m hm χ
  have a := h.2 χ _ (𝟙 _) z J J' hJ hJ'
  have b := h.2 (p.xe χ) _ m z J J' hJ hJ'
  have d := val_of_pmaps o (ht χ) (𝟙 _) hJ' hJ'
  rw [Category.id_comp] at a d
  rw [d] at b
  refine (congrArg (fun x => val ((Φ Y (𝟙 Y)).s (hE.xe x)) (m ≫ φ) z J) (hp.1 χ)).symm.trans (b.trans (Eq.trans ?_ a.symm))
  refine (_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (· * ·) (prod_cocycle E.toPre.P.isAb hc D.P.isLB E.toPre.P.isLB
    ((isGen_iff _).1 hE.w_gen) ((isGen_iff _).1 p.w_gen) (fun k => 𝟙 _ ≫ E.toPre.Oφ c.pG χ k) _ (fun k => ?_)
    (fun k => (Category.assoc _ _ _).trans ((Category.id_comp _).trans (o k))) hJ hJ') rfl)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm)
  fin_cases k
  exacts [(Over.w _).trans (Over.w c.pG).symm, (Over.w _).trans (Over.w c.pG).symm, rfl,
    (Over.w _).trans (Over.w c.pG).symm]

end Model

theorem exists_model : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom ∧ (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap ρ)) ∧ (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) ∧ (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ a.act σ ∧ h ≫ φ e = φ e) := by
  intro R _ _ _ hR R' _ _ _ ρ D D' hD A' G' _ _ U' a
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨Y, _, _, Φ, hΦ, hY, -⟩ := GlobalTheory.ExtensionMul.exists_represents_pow R D.toPre
  choose φ hφ using fun e => exists_carries hD hΦ (U'.gt e)
  refine ⟨Y, φ, hY, fun e => (hφ e).isPullback hΦ U'.toUnifPre, fun e => (hφ e).succ hΦ U'.toUnifPre (hφ (e + 1)),
    fun e σ => ?_⟩
  obtain ⟨p, bc, hbc, ⟨_, -, _, -, hl⟩, hp⟩ := a.unif σ
  obtain ⟨m, h₁, h₂, h₃, -⟩ := hl e
  refine ⟨m, by rw [← hbc]; exact h₁, (hφ e).invariant hΦ p hp h₂ fun x => ?_⟩
  obtain ⟨hψ, H⟩ := h₃ x
  exact (maps_iff p.w _ _ _ _ _ m _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 H

end GlobalTheory.FormalModel

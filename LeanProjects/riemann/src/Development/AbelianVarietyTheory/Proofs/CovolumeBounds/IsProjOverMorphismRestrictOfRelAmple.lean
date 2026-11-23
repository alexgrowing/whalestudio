import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus PolAV RelAmple VeryAmpleAt powOver)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG LBIso IsProjOver)
open ReciprocityTheory.ChartRestriction.G.DVR.SecOps (secScale)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.AbLaw

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

variable {R : Type} [CommRing R] {M : ℕ} {Y Z : Scheme.{0}} {L L' : LB Y}

theorem isUnit_resG_sec (a : L.Sec) (k : L.ι) {W : Y.Opens} (ha : W ≤ nonzeroLocus a) (hk : W ≤ L.U k) :
    IsUnit (resG Y hk (a.f k)) := by
  have h : W ≤ Y.basicOpen (a.f k) := (le_inf ha hk).trans (nonzeroLocus_inf_chart a k).le
  have := (Y.toRingedSpace.isUnit_res_basicOpen (a.f k)).map (resG Y h)
  exact (congrArg IsUnit (resG_resG (Y.basicOpen_le (a.f k)) h (a.f k))).mp this

theorem le_nonzeroLocus_of_isUnit (a : L.Sec) (k : L.ι) {W : Y.Opens} (hk : W ≤ L.U k)
    (h : IsUnit (resG Y hk (a.f k))) : W ≤ nonzeroLocus a := by
  have := Y.basicOpen_of_isUnit h
  rw [Scheme.basicOpen_res] at this
  exact (this.ge.trans inf_le_right).trans (basicOpen_le_nonzeroLocus a k)

theorem ext_charts (a : L.Sec) {W : Y.Opens} (ha : W ≤ nonzeroLocus a) {r r' : Γ(Y, W)}
    (h : ∀ k, resG Y (inf_le_left : W ⊓ L.U k ≤ W) r = resG Y inf_le_left r') : r = r' :=
  ext_germ fun y hy => by
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (ha hy)
    have hm : y ∈ W ⊓ L.U k := ⟨hy, hk⟩
    have := congrArg (Y.presheaf.germ (W ⊓ L.U k) y hm).hom (h k)
    rwa [germ_resG, germ_resG] at this

theorem exists_secRatio (a b : L.Sec) : ∃ r : Γ(Y, nonzeroLocus a), ∀ k,
    resG Y (inf_le_right : nonzeroLocus a ⊓ L.U k ≤ L.U k) (b.f k) =
      resG Y inf_le_left r * resG Y inf_le_right (a.f k) := by
  have loc : ∀ k, ∃ c : Γ(Y, nonzeroLocus a ⊓ L.U k),
      resG Y inf_le_right (b.f k) = c * resG Y inf_le_right (a.f k) := fun k =>
    ((isUnit_resG_sec a k inf_le_left inf_le_right).dvd).imp fun c hc => hc.trans (mul_comm _ _)
  choose c hc using loc
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun k => nonzeroLocus a ⊓ L.U k) (nonzeroLocus a)
    (fun _ => homOfLE inf_le_left)
    (fun y hy => (exists_chart_of_mem_nonzeroLocus hy).elim fun k hk => Opens.mem_iSup.2 ⟨k, hy, hk⟩) c
    (fun k l => by
      have hk : nonzeroLocus a ⊓ L.U k ⊓ (nonzeroLocus a ⊓ L.U l) ≤ L.U k := inf_le_left.trans inf_le_right
      have hl : nonzeroLocus a ⊓ L.U k ⊓ (nonzeroLocus a ⊓ L.U l) ≤ L.U l := inf_le_right.trans inf_le_right
      have e₁ := congrArg (resG Y (inf_le_left : _ ⊓ (nonzeroLocus a ⊓ L.U l) ≤ _)) (hc k)
      have e₂ := congrArg (resG Y (inf_le_right : (nonzeroLocus a ⊓ L.U k) ⊓ _ ≤ _)) (hc l)
      rw [map_mul, resG_resG, resG_resG] at e₁ e₂
      refine (isUnit_resG_sec a k (inf_le_left.trans inf_le_left) hk).mul_right_cancel (e₁.symm.trans ?_)
      rw [sec_compat b k l hk hl, sec_compat a k l hk hl, e₂]
      exact mul_left_comm _ _ _)
  exact ⟨r, fun k => (hc k).trans (congrArg (· * _) (hr k).symm)⟩

def secRatio (a b : L.Sec) : Γ(Y, nonzeroLocus a) := (exists_secRatio a b).choose

theorem secRatio_spec (a b : L.Sec) (k : L.ι) :
    resG Y (inf_le_right : nonzeroLocus a ⊓ L.U k ≤ L.U k) (b.f k) =
      resG Y inf_le_left (secRatio a b) * resG Y inf_le_right (a.f k) :=
  (exists_secRatio a b).choose_spec k

theorem secRatio_on (a b : L.Sec) (k : L.ι) {W : Y.Opens} (ha : W ≤ nonzeroLocus a) (hk : W ≤ L.U k) :
    resG Y hk (b.f k) = resG Y ha (secRatio a b) * resG Y hk (a.f k) := by
  have := congrArg (resG Y (le_inf ha hk)) (secRatio_spec a b k)
  rwa [map_mul, resG_resG, resG_resG, resG_resG] at this

theorem eq_resG_secRatio (a b : L.Sec) {W : Y.Opens} (ha : W ≤ nonzeroLocus a) {r : Γ(Y, W)}
    (h : ∀ k, resG Y (inf_le_right : W ⊓ L.U k ≤ L.U k) (b.f k) =
      resG Y inf_le_left r * resG Y inf_le_right (a.f k)) : r = resG Y ha (secRatio a b) :=
  ext_charts a ha fun k => by
    refine (isUnit_resG_sec a k (inf_le_left.trans ha) inf_le_right).mul_right_cancel ?_
    rw [← h k, resG_resG]
    exact secRatio_on a b k _ _

theorem eq_secRatio (a b : L.Sec) {r : Γ(Y, nonzeroLocus a)}
    (h : ∀ k, resG Y (inf_le_right : nonzeroLocus a ⊓ L.U k ≤ L.U k) (b.f k) =
      resG Y inf_le_left r * resG Y inf_le_right (a.f k)) : r = secRatio a b :=
  (eq_resG_secRatio a b le_rfl h).trans (resG_self _ _)

@[simp] theorem secRatio_self (a : L.Sec) : secRatio a a = 1 :=
  (eq_secRatio a a fun _ => by rw [map_one, one_mul]).symm

theorem secRatio_mul_secRatio (a b c : L.Sec) {W : Y.Opens} (ha : W ≤ nonzeroLocus a)
    (hb : W ≤ nonzeroLocus b) :
    resG Y ha (secRatio a b) * resG Y hb (secRatio b c) = resG Y ha (secRatio a c) :=
  eq_resG_secRatio a c ha fun k => by
    rw [map_mul, resG_resG, resG_resG, secRatio_on b c k (inf_le_left.trans hb),
      secRatio_on a b k (inf_le_left.trans ha)]
    ring

theorem basicOpen_secRatio (a b : L.Sec) :
    Y.basicOpen (secRatio a b) = nonzeroLocus a ⊓ nonzeroLocus b := by
  have key : ∀ y (hy : y ∈ nonzeroLocus a), y ∈ Y.basicOpen (secRatio a b) ↔ y ∈ nonzeroLocus b := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
    have hm : y ∈ nonzeroLocus a ⊓ L.U k := ⟨hy, hk⟩
    have e := congrArg (Y.presheaf.germ _ y hm).hom (secRatio_spec a b k)
    rw [map_mul, germ_resG, germ_resG, germ_resG] at e
    have hu := (Y.mem_basicOpen _ y hk).1 ((mem_nonzeroLocus_iff a k hk).1 hy)
    rw [mem_nonzeroLocus_iff b k hk, Y.mem_basicOpen _ y hk, Y.mem_basicOpen _ y hy]
    refine Iff.trans ?_ (iff_of_eq (congrArg IsUnit e)).symm
    rw [IsUnit.mul_iff]
    exact ⟨fun h => ⟨h, hu⟩, fun h => h.1⟩
  ext y
  exact ⟨fun h => ⟨Y.basicOpen_le _ h, (key y (Y.basicOpen_le _ h)).1 h⟩, fun h => (key y h.1).2 h.2⟩

theorem isCoordFamily_secRatio {s : Fin (M + 1) → L.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤) :
    IsCoordFamily (fun i => nonzeroLocus (s i)) (fun i j => secRatio (s i) (s j)) where
  cover := hs
  self _ := secRatio_self _
  mul _ _ _ := secRatio_mul_secRatio _ _ _ _ _
  basicOpen_le _ _ := (basicOpen_secRatio _ _).le.trans inf_le_right

def toProj (f : Y ⟶ Sp R) (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤) : Y ⟶ PSpace R M :=
  (isCoordFamily_secRatio hs).toHom f

section

variable (f : Y ⟶ Sp R) (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)

@[reassoc] theorem toProj_str : toProj f s hs ≫ PSpace.str R M = f :=
  (isCoordFamily_secRatio hs).toHom_str f

theorem toProj_preimage_chart (i : Fin (M + 1)) : toProj f s hs ⁻¹ᵁ chart R M i = nonzeroLocus (s i) :=
  (isCoordFamily_secRatio hs).toHom_preimage f i

theorem pullRatio_toProj (i j : Fin (M + 1)) :
    pullRatio (toProj f s hs) (nonzeroLocus (s i)) i (toProj_preimage_chart f s hs i).ge j =
      secRatio (s i) (s j) :=
  (isCoordFamily_secRatio hs).pullRatio_toHom f i j

theorem pullRatio_toProj_on (i j : Fin (M + 1)) {W : Y.Opens} (h : W ≤ toProj f s hs ⁻¹ᵁ chart R M i) :
    pullRatio (toProj f s hs) W i h j =
      resG Y (h.trans (toProj_preimage_chart f s hs i).le) (secRatio (s i) (s j)) := by
  rw [← pullRatio_toProj f s hs, resG_pullRatio]

theorem sec_eq_pullRatio_toProj_mul (i j : Fin (M + 1)) (k : L.ι) {W : Y.Opens}
    (h : W ≤ toProj f s hs ⁻¹ᵁ chart R M i) (hk : W ≤ L.U k) :
    resG Y hk ((s j).f k) = pullRatio (toProj f s hs) W i h j * resG Y hk ((s i).f k) := by
  rw [pullRatio_toProj_on]
  exact secRatio_on _ _ k _ hk

variable {f s}

theorem eq_toProj_of_locally {φ : Y ⟶ PSpace R M} (hφ : φ ≫ PSpace.str R M = f)
    (H : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (k : L.ι) (hk : W ≤ L.U k) (i : Fin (M + 1))
      (hi : W ≤ φ ⁻¹ᵁ chart R M i) (u : Γ(Y, W)), ∀ j, resG Y hk ((s j).f k) = u * pullRatio φ W i hi j) :
    φ = toProj f s hs := by
  refine hom_ext (hφ.trans (toProj_str f s hs).symm) fun y => ?_
  obtain ⟨W, hy, k, hk, i, hi, u, e⟩ := H y
  have hu : resG Y hk ((s i).f k) = u := by rw [e i, pullRatio_self, mul_one]
  have hyi : y ∈ nonzeroLocus (s i) := by
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
    have h1 := (Y.mem_basicOpen _ y (hk hy)).1 ((mem_nonzeroLocus_iff _ k (hk hy)).1 hj)
    have h2 := congrArg (Y.presheaf.germ W y hy).hom (e j)
    rw [← hu, map_mul, germ_resG, germ_resG] at h2
    exact (mem_nonzeroLocus_iff _ k (hk hy)).2 ((Y.mem_basicOpen _ y (hk hy)).2
      (isUnit_of_mul_isUnit_left ((congrArg IsUnit h2).mp h1)))
  have h₂ : W ⊓ nonzeroLocus (s i) ≤ toProj f s hs ⁻¹ᵁ chart R M i :=
    inf_le_right.trans (toProj_preimage_chart f s hs i).ge
  refine ⟨W ⊓ nonzeroLocus (s i), ⟨hy, hyi⟩, i, inf_le_left.trans hi, h₂, fun j => ?_⟩
  refine (isUnit_resG_sec (s i) k inf_le_right (inf_le_left.trans hk)).mul_right_cancel ?_
  have e' := congrArg (resG Y (inf_le_left : W ⊓ nonzeroLocus (s i) ≤ W)) (e j)
  rw [← hu, map_mul, resG_resG, resG_resG, resG_pullRatio] at e'
  rw [← sec_eq_pullRatio_toProj_mul f s hs i j k h₂, e', mul_comm]

theorem eq_toProj_of_pullRatio {φ : Y ⟶ PSpace R M} (hφ : φ ≫ PSpace.str R M = f)
    (h : ∀ i, nonzeroLocus (s i) ≤ φ ⁻¹ᵁ chart R M i)
    (H : ∀ i j, pullRatio φ (nonzeroLocus (s i)) i (h i) j = secRatio (s i) (s j)) :
    φ = toProj f s hs := by
  refine hom_ext (hφ.trans (toProj_str f s hs).symm) fun y => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  exact ⟨_, hi, i, h i, (toProj_preimage_chart f s hs i).ge, fun j =>
    (H i j).trans (pullRatio_toProj f s hs i j).symm⟩

end

theorem resG_secPull_coord (φ : Y ⟶ PSpace R M) (j : Fin (M + 1)) (i : PUnit → Fin (M + 1)) {W : Y.Opens}
    (h : W ≤ ((O1 R M).pull φ).U i) :
    resG Y h ((secPull (coord R M j) φ).f i) =
      pullRatio φ W (i ⟨⟩) (h.trans (pull_U (O1 R M) φ i).le) j :=
  resG_resG _ _ _

theorem restrict_pullback_O1_transition (φ : Y ⟶ PSpace R M) (i j : PUnit → Fin (M + 1)) {W : Y.Opens}
    (hi : W ≤ ((O1 R M).pull φ).U i) (hj : W ≤ ((O1 R M).pull φ).U j) :
    resG Y (le_inf hi hj) (((O1 R M).pull φ).g i j).val =
      pullRatio φ W (i ⟨⟩) (hi.trans (pull_U (O1 R M) φ i).le) (j ⟨⟩) := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R M (i ⟨⟩) ⊓ chart R M (j ⟨⟩)) :=
    le_inf (hi.trans (pull_U (O1 R M) φ i).le) (hj.trans (pull_U (O1 R M) φ j).le)
  refine (congrArg (fun u => resG Y (le_inf hi hj) (Units.val u)) (pull_g (O1 R M) φ i j)).trans ?_
  exact (resG_resG _ _ _).trans (appLE_ratioOn inf_le_left hW)

theorem iSup_nonzeroLocus_secPull {s : Fin (M + 1) → L.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (g : Z ⟶ Y) :
    ⨆ i, nonzeroLocus (secPull (s i) g) = ⊤ := by
  simp only [nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup, hs]
  rfl

section

variable (f : Y ⟶ Sp R) (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)

theorem pullback_O1_toProj_chart (i : PUnit → Fin (M + 1)) :
    ((O1 R M).pull (toProj f s hs)).U i = nonzeroLocus (s (i ⟨⟩)) :=
  (pull_U (O1 R M) _ i).trans (toProj_preimage_chart f s hs _)

def toProjIso : LB.Iso ((O1 R M).pull (toProj f s hs)) L where
  s p := (isUnit_resG_sec (s (p.2 ⟨⟩)) p.1
    (inf_le_right.trans (pullback_O1_toProj_chart f s hs p.2).le) inf_le_left).unit

theorem val_toProjIso (k : L.ι) (i : PUnit → Fin (M + 1)) :
    (@id (Γ(Y, L.U k ⊓ ((O1 R M).pull (toProj f s hs)).U i)ˣ) ((toProjIso f s hs).s (k, i))).val =
      resG Y inf_le_left ((s (i ⟨⟩)).f k) := rfl

theorem secMaps_toProjIso (j : Fin (M + 1)) :
    SecMaps (toProjIso f s hs) (secPull (coord R M j) (toProj f s hs)) (s j) := by
  rintro ⟨k, i⟩
  exact (sec_eq_pullRatio_toProj_mul f s hs (i ⟨⟩) j k _ inf_le_left).trans ((mul_comm _ _).trans
    (congrArg (_ * ·) (resG_secPull_coord (toProj f s hs) j i inf_le_right).symm))

theorem toProjIso_isGen : (toProjIso f s hs).IsGen := by
  rintro ⟨p, q⟩ ⟨p', q'⟩
  let A := (O1 R M).pull (toProj f s hs)
  have hp : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ L.U p := inf_le_left.trans inf_le_left
  have hq : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
  have hp' : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ L.U p' := inf_le_right.trans inf_le_left
  have hq' : L.U p ⊓ A.U q ⊓ (L.U p' ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (@id (Γ(Y, L.U p ⊓ A.U q)ˣ) ((toProjIso f s hs).s (p, q))) *
      res (le_inf hq hq') (A.g q q') = res (le_inf hp hp') (L.g p p') *
        res (le_inf hp' hq') (@id (Γ(Y, L.U p' ⊓ A.U q')ˣ) ((toProjIso f s hs).s (p', q'))) := by
    refine Units.ext ?_
    change resG Y (le_inf hp hq) (resG Y inf_le_left ((s (q ⟨⟩)).f p)) * resG Y (le_inf hq hq') (A.g q q').val =
      resG Y (le_inf hp hp') (L.g p p').val * resG Y (le_inf hp' hq') (resG Y inf_le_left ((s (q' ⟨⟩)).f p'))
    rw [resG_resG, resG_resG, ← sec_compat _ p p' hp hp']
    exact (congrArg (_ * ·) (restrict_pullback_O1_transition (toProj f s hs) q q' hq hq')).trans ((mul_comm _ _).trans
      (sec_eq_pullRatio_toProj_mul f s hs (q ⟨⟩) (q' ⟨⟩) p _ hp).symm)
  change res (le_inf hp hq) (@id (Γ(Y, L.U p ⊓ A.U q)ˣ) ((toProjIso f s hs).s (p, q))) =
    res (le_inf hp hp') (L.g p p') * (res (le_inf hq hq') (A.g q q'))⁻¹ *
      res (le_inf hp' hq') (@id (Γ(Y, L.U p' ⊓ A.U q')ˣ) ((toProjIso f s hs).s (p', q')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

theorem lbIso_pullback_O1_toProj : LBIso ((O1 R M).pull (toProj f s hs)) L :=
  ⟨toProjIso f s hs, toProjIso_isGen f s hs⟩

theorem eq_toProjIso {w : LB.Iso ((O1 R M).pull (toProj f s hs)) L}
    (hw : ∀ j, SecMaps w (secPull (coord R M j) (toProj f s hs)) (s j)) : w = toProjIso f s hs := by
  obtain ⟨w⟩ := w
  refine congrArg LB.Gen.mk (funext ?_)
  rintro ⟨k, i⟩
  have e := hw (i ⟨⟩) (k, i)
  have e' := (resG_secPull_coord (toProj f s hs) (i ⟨⟩) i
    (inf_le_right : L.U k ⊓ _ ≤ _)).trans pullRatio_self
  exact Units.ext (e.trans ((congrArg (_ * ·) e').trans (mul_one _))).symm

variable {f s}

include hs in

theorem exists_chart_of_iSup_nonzeroLocus (y : Y) : ∃ k, y ∈ L.U k :=
  (Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))).elim fun _ h => exists_chart_of_mem_nonzeroLocus h

theorem eq_toProj_of_secMaps {φ : Y ⟶ PSpace R M} (hφ : φ ≫ PSpace.str R M = f)
    {w : LB.Iso ((O1 R M).pull φ) L} (hw : ∀ j, SecMaps w (secPull (coord R M j) φ) (s j)) :
    φ = toProj f s hs := by
  refine eq_toProj_of_locally hs hφ fun y => ?_
  obtain ⟨k, hk⟩ := exists_chart_of_iSup_nonzeroLocus hs y
  obtain ⟨i, hi⟩ := exists_mem_chart R M (φ y)
  have hi' : y ∈ ((O1 R M).pull φ).U fun _ => i := (pull_U (O1 R M) φ fun _ => i).ge hi
  exact ⟨L.U k ⊓ ((O1 R M).pull φ).U fun _ => i, ⟨hk, hi'⟩, k, inf_le_left, i, _, _, fun j =>
    (hw j (k, fun _ => i)).trans (congrArg (_ * ·) (resG_secPull_coord φ j (fun _ => i) inf_le_right))⟩

end

section

variable {f : Y ⟶ Sp R} {s : Fin (M + 1) → L.Sec} (hs : ⨆ i, nonzeroLocus (s i) = ⊤)

theorem toProj_eq_comp_of_locally (g : Z ⟶ Y) {B : LB Z} {t : Fin (M + 1) → B.Sec}
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
    (H : ∀ z : Z, ∃ (W : Z.Opens) (_ : z ∈ W) (k : L.ι) (hk : W ≤ g ⁻¹ᵁ L.U k) (l : B.ι) (hl : W ≤ B.U l)
      (u : Γ(Z, W)), ∀ j, resG Z hl ((t j).f l) = u * (g.appLE _ W hk).hom ((s j).f k)) :
    toProj (g ≫ f) t ht = g ≫ toProj f s hs := by
  refine (eq_toProj_of_locally ht (by rw [Category.assoc, toProj_str]) fun z => ?_).symm
  obtain ⟨W, hz, k, hk, l, hl, u, e⟩ := H z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (g z)))
  have h₁ : nonzeroLocus (s i) ⊓ L.U k ≤ toProj f s hs ⁻¹ᵁ chart R M i :=
    inf_le_left.trans (toProj_preimage_chart f s hs i).ge
  have h₂ : W ⊓ g ⁻¹ᵁ nonzeroLocus (s i) ≤ g ⁻¹ᵁ (nonzeroLocus (s i) ⊓ L.U k) :=
    le_inf inf_le_right (inf_le_left.trans hk)
  refine ⟨W ⊓ g ⁻¹ᵁ nonzeroLocus (s i), ⟨hz, hi⟩, l, inf_le_left.trans hl, i,
    h₂.trans (g.preimage_mono h₁), resG Z inf_le_left u * (g.appLE _ _ (inf_le_left.trans hk)).hom ((s i).f k),
    fun j => ?_⟩
  have e₁ := congrArg (resG Z (inf_le_left : W ⊓ g ⁻¹ᵁ nonzeroLocus (s i) ≤ W)) (e j)
  have e₂ := congrArg (g.appLE _ _ h₂).hom (sec_eq_pullRatio_toProj_mul f s hs i j k h₁ inf_le_right)
  rw [map_mul, resG_resG, resG_appLE] at e₁
  rw [map_mul, appLE_resG, appLE_resG, appLE_pullRatio] at e₂
  rw [e₁, e₂, mul_assoc, mul_comm (pullRatio _ _ _ _ _)]

theorem toProj_eq_of_locally {t : Fin (M + 1) → L'.Sec} (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
    (H : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (k : L.ι) (hk : W ≤ L.U k) (l : L'.ι) (hl : W ≤ L'.U l)
      (u : Γ(Y, W)), ∀ j, resG Y hl ((t j).f l) = u * resG Y hk ((s j).f k)) :
    toProj f t ht = toProj f s hs :=
  toProj_eq_comp_of_locally (f := f) hs (𝟙 Y) ht H

include hs in

theorem iSup_nonzeroLocus_secScale (u : Γ(Y, ⊤)ˣ) : ⨆ i, nonzeroLocus (secScale u.val (s i)) = ⊤ := by
  simp only [nonzeroLocus_secScale, Y.basicOpen_of_isUnit u.isUnit, top_inf_eq, hs]

theorem toProj_secScale (u : Γ(Y, ⊤)ˣ) :
    toProj f (fun i => secScale u.val (s i)) (iSup_nonzeroLocus_secScale hs u) = toProj f s hs :=
  toProj_eq_of_locally hs _ fun y => (exists_chart_of_iSup_nonzeroLocus hs y).elim fun k hk =>
    ⟨L.U k, hk, k, le_rfl, k, le_rfl, resG Y le_top u.val, fun _ =>
      (resG_self _ _).trans (congrArg (_ * ·) (resG_self _ _).symm)⟩

theorem toProj_eq_of_secMaps {t : Fin (M + 1) → L'.Sec} (ht : ⨆ i, nonzeroLocus (t i) = ⊤)
    {w : LB.Iso L L'} (hw : ∀ j, SecMaps w (s j) (t j)) : toProj f t ht = toProj f s hs := by
  refine toProj_eq_of_locally hs ht fun y => ?_
  obtain ⟨k, hk⟩ := exists_chart_of_iSup_nonzeroLocus hs y
  obtain ⟨l, hl⟩ := exists_chart_of_iSup_nonzeroLocus ht y
  exact ⟨L'.U l ⊓ L.U k, ⟨hl, hk⟩, k, inf_le_right, l, inf_le_left, _, fun j => hw j (l, k)⟩

include hs in

theorem iSup_nonzeroLocus_of_secMaps (hL : L.IsLB) (hL' : L'.IsLB) {t : Fin (M + 1) → L'.Sec}
    {w : LB.Iso L L'} (hw : ∀ j, SecMaps w (s j) (t j)) : ⨆ i, nonzeroLocus (t i) = ⊤ :=
  (iSup_congr fun i => ((hw i).nonzeroLocus_eq hL hL').symm).trans hs

theorem toProj_secPull (g : Z ⟶ Y) :
    toProj (g ≫ f) (fun i => secPull (s i) g) (iSup_nonzeroLocus_secPull hs g) = g ≫ toProj f s hs :=
  toProj_eq_comp_of_locally hs g _ fun z => (exists_chart_of_iSup_nonzeroLocus hs (g z)).elim fun k hk =>
    ⟨g ⁻¹ᵁ L.U k, hk, k, le_rfl, fun _ => k, (pull_U L g fun _ => k).ge, 1, fun _ =>
      (resG_resG _ _ _).trans (one_mul _).symm⟩

theorem toProj_eq_comp_of_secMaps (g : Z ⟶ Y) {B : LB Z} {t : Fin (M + 1) → B.Sec}
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) {w : LB.Iso (L.pull g) B}
    (hw : ∀ j, SecMaps w (secPull (s j) g) (t j)) : toProj (g ≫ f) t ht = g ≫ toProj f s hs :=
  (toProj_eq_of_secMaps (iSup_nonzeroLocus_secPull hs g) ht hw).trans (toProj_secPull hs g)

end

variable (R M) in

theorem toProj_coord :
    toProj (PSpace.str R M) (coord R M) (iSup_nonzeroLocus_coord R M) = 𝟙 (PSpace R M) :=
  (eq_toProj_of_locally _ (Category.id_comp _) fun y => (exists_mem_chart R M y).elim fun i hi =>
    ⟨chart R M i, hi, i, le_rfl, i, le_rfl, 1, fun _ => (one_mul _).symm⟩).symm

theorem toProj_secPull_coord (φ : Y ⟶ PSpace R M) :
    toProj (φ ≫ PSpace.str R M) (fun i => secPull (coord R M i) φ)
      (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R M) φ) = φ := by
  rw [toProj_secPull (iSup_nonzeroLocus_coord R M), toProj_coord, Category.comp_id]

theorem pullRatio_comp_baseChange {R' : Type} [CommRing R'] (c : R →+* R') (φ : Y ⟶ PSpace R' M)
    {W : Y.Opens} {i : Fin (M + 1)} (h : W ≤ (φ ≫ baseChange M c) ⁻¹ᵁ chart R M i)
    (h' : W ≤ φ ⁻¹ᵁ chart R' M i) (j : Fin (M + 1)) :
    pullRatio (φ ≫ baseChange M c) W i h j = pullRatio φ W i h' j := by
  have e : pullRatio (baseChange M c) (chart R' M i) i (baseChange_preimage_chart M c i).ge j =
      ratio R' M i j :=
    congrArg (resG _ (baseChange_preimage_chart M c i).ge) (baseChange_app_ratioOn c le_rfl j)
  rw [← appLE_pullRatio (hi := (baseChange_preimage_chart M c i).ge) φ h', e]
  rfl

theorem toProj_baseChange {R' : Type} [CommRing R'] (c : R →+* R') (f : Y ⟶ Sp R')
    (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤) :
    toProj f s hs ≫ baseChange M c = toProj (f ≫ spMap c) s hs := by
  have h : ∀ i, nonzeroLocus (s i) ≤ (toProj f s hs ≫ baseChange M c) ⁻¹ᵁ chart R M i := fun i => by
    rw [Scheme.Hom.comp_preimage, baseChange_preimage_chart, toProj_preimage_chart]
  refine eq_toProj_of_pullRatio hs ?_ h fun i j => ?_
  · rw [Category.assoc, baseChange_str, toProj_str_assoc]
  · exact (pullRatio_comp_baseChange c _ _ _ j).trans (pullRatio_toProj f s hs i j)

theorem isClosedImmersion_toProj_iff (f : Y ⟶ Sp R) (s : Fin (M + 1) → L.Sec)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) :
    IsClosedImmersion (toProj f s hs) ↔ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ Function.Surjective
      (eval₂Hom (baseRingHom f (nonzeroLocus (s i))).hom fun j => secRatio (s i) (s j)) := by
  rw [isClosedImmersion_iff_pullRatio _ (toProj_preimage_chart f s hs), toProj_str]
  refine forall_congr' fun i => ?_
  rw [funext (pullRatio_toProj f s hs i)]

theorem veryAmpleBy_iff (f : Y ⟶ Sp R) (s : Fin (M + 1) → L.Sec) :
    VeryAmpleBy f L s ↔ ∃ hs : ⨆ i, nonzeroLocus (s i) = ⊤, IsClosedImmersion (toProj f s hs) := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, (isClosedImmersion_toProj_iff f s hs).2 fun i => ⟨(H i).1, ?_⟩⟩
    obtain ⟨r, hr, hsurj⟩ := (H i).2
    obtain rfl : r = fun j => secRatio (s i) (s j) := funext fun j => eq_secRatio _ _ (hr j)
    exact hsurj
  · rintro ⟨hs, H⟩
    have H' := (isClosedImmersion_toProj_iff f s hs).1 H
    exact ⟨hs, fun i => ⟨(H' i).1, _, fun j => secRatio_spec (s i) (s j), (H' i).2⟩⟩

theorem isProjOver_of_veryAmpleBy {f : Y ⟶ Sp R} {s : Fin (M + 1) → L.Sec} (h : VeryAmpleBy f L s) :
    IsProjOver f := by
  obtain ⟨hs, H⟩ := (veryAmpleBy_iff f s).1 h
  exact ⟨M, toProj f s hs, H, toProj_str f s hs⟩

theorem veryAmpleBy_secPull_coord (φ : Y ⟶ PSpace R M) [IsClosedImmersion φ] :
    VeryAmpleBy (φ ≫ PSpace.str R M) ((O1 R M).pull φ) fun i => secPull (coord R M i) φ :=
  (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R M) φ, by
    rwa [toProj_secPull_coord]⟩

theorem isProjBy_iff_isProjOver (f : Y ⟶ Sp R) : IsProjBy f ↔ IsProjOver f := by
  constructor
  · rintro ⟨_, _, _, _, h⟩
    exact isProjOver_of_veryAmpleBy h
  · rintro ⟨N, φ, _, rfl⟩
    exact ⟨_, LB.isLB_pull (O1_isLB R N) φ, N, _, veryAmpleBy_secPull_coord φ⟩

theorem veryAmpleBy_comp_iff {T : Scheme.{0}} (q : Y ⟶ T) (e : T ⟶ Sp R) [IsIso e] (s : Fin (M + 1) → L.Sec) :
    VeryAmpleBy (q ≫ e) L s ↔
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ(Y, nonzeroLocus (s i)),
          (∀ j k, resG _ (inf_le_right : nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
            resG _ inf_le_left (r j) * resG _ inf_le_right ((s i).f k)) ∧
          Function.Surjective (eval₂Hom (q.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r) := by
  refine and_congr_right fun _ => forall_congr' fun i => and_congr_right fun _ =>
    exists_congr fun r => and_congr_right fun _ => ?_
  have h : eval₂Hom (cst (q ≫ e) (nonzeroLocus (s i))) r =
      (eval₂Hom (q.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r).comp
        (MvPolynomial.map (baseRingHom e ⊤).hom) := by
    refine ringHom_ext (fun a => ?_) (fun j => by simp)
    rw [RingHom.comp_apply, map_C, eval₂Hom_C, eval₂Hom_C]
    exact congrArg (fun ψ => ψ.hom a) (baseRingHom_appLE e q ⊤ (nonzeroLocus (s i)) le_top).symm
  have : IsIso (baseRingHom e ⊤) := by
    rw [baseRingHom_top]
    have : IsIso e.appTop := inferInstanceAs (IsIso (e.app ⊤))
    infer_instance
  rw [h, RingHom.coe_comp]
  exact Function.Surjective.of_comp_iff _
    (map_surjective _ (ConcreteCategory.bijective_of_isIso (baseRingHom e ⊤)).2)

theorem isProjOver_of_isIso_comp (g : Z ⟶ Y) [IsIso g] {f : Y ⟶ Sp R} (h : IsProjOver (g ≫ f)) :
    IsProjOver f := by
  obtain ⟨N, φ, _, e⟩ := h
  exact ⟨N, inv g ≫ φ, inferInstance, by rw [Category.assoc, e, IsIso.inv_hom_id_assoc]⟩

section Group

attribute [local instance] Over.cartesianMonoidalCategory

theorem isProjOver_morphismRestrict_of_relAmple {S : Scheme.{0}} {A : Over S} [GrpObj A] {B : LB A.left}
    (h : RelAmple A B) {U : S.Opens} (hU : IsAffineOpen U) :
    IsProjOver (R := Γ(S, U)) (A.hom ∣_ U ≫ hU.isoSpec.hom) := by
  obtain ⟨N, -, M, s, H⟩ := h U hU
  exact isProjOver_of_veryAmpleBy ((veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).2 H)

theorem veryAmpleAt_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] (B : LB A.left) (N : ℕ) :
    VeryAmpleAt A B N ↔ ∀ (U : S.Opens) (hU : IsAffineOpen U), ∃ (M : ℕ)
      (s : Fin (M + 1) → (powOver A B U N).Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤),
      IsClosedImmersion (toProj (R := Γ(S, U)) (A.hom ∣_ U ≫ hU.isoSpec.hom) s hs) :=
  forall₂_congr fun U hU => exists₂_congr fun _ s =>
    (veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).symm.trans (veryAmpleBy_iff _ s)

theorem relAmple_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] (B : LB A.left) :
    RelAmple A B ↔ ∀ (U : S.Opens) (hU : IsAffineOpen U), ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ)
      (s : Fin (M + 1) → (powOver A B U N).Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤),
      IsClosedImmersion (toProj (R := Γ(S, U)) (A.hom ∣_ U ≫ hU.isoSpec.hom) s hs) :=
  forall₂_congr fun U hU => exists_congr fun _ => and_congr_right fun _ => exists₂_congr fun _ s =>
    (veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).symm.trans (veryAmpleBy_iff _ s)

theorem isProjOver_of_relAmple {A : Over (Sp R)} [GrpObj A] {B : LB A.left} (h : RelAmple A B) :
    IsProjOver A.hom := by
  obtain ⟨N, -, M, s, H⟩ := h ⊤ (isAffineOpen_top _)
  have : IsIso (⊤ : (Sp R).Opens).ι := inferInstanceAs (IsIso (Sp R).topIso.hom)
  have : IsIso (A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso A.left.topIso.hom)
  have h' := isProjOver_of_veryAmpleBy ((veryAmpleBy_comp_iff (A.hom ∣_ ⊤) (⊤ : (Sp R).Opens).ι s).2 H)
  rw [morphismRestrict_ι] at h'
  exact isProjOver_of_isIso_comp _ h'

theorem isProjOver_polAV (P : PolAV (Sp R)) : IsProjOver P.A.hom :=
  isProjOver_of_relAmple P.ample

end Group

theorem toProj_spec (f : Y ⟶ Sp R) (s : Fin (M + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤) :
    toProj f s hs ≫ PSpace.str R M = f ∧
    (∃ h : ∀ i, toProj f s hs ⁻¹ᵁ Proj.basicOpen (grading R M) (X i) = nonzeroLocus (s i),
      ∀ i j k, resG Y (inf_le_right : nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
        resG Y inf_le_left (((toProj f s hs).appLE (chart R M i) _ (h i).ge).hom (ratio R M i j)) *
          resG Y inf_le_right ((s i).f k)) ∧
    (∃! w : LB.Iso ((O1 R M).pull (toProj f s hs)) L,
      w.IsGen ∧ ∀ j, SecMaps w (secPull (coord R M j) (toProj f s hs)) (s j)) ∧
    (∀ (φ : Y ⟶ PSpace R M) (w : LB.Iso ((O1 R M).pull φ) L), φ ≫ PSpace.str R M = f →
      (∀ j, SecMaps w (secPull (coord R M j) φ) (s j)) → φ = toProj f s hs) ∧
    (∀ u : Γ(Y, ⊤)ˣ, ∃ hu : ⨆ i, nonzeroLocus (secScale u.val (s i)) = ⊤,
      toProj f (fun i => secScale u.val (s i)) hu = toProj f s hs) ∧
    (∀ (B : LB Y) (t : Fin (M + 1) → B.Sec) (w : LB.Iso L B), L.IsLB → B.IsLB →
      (∀ j, SecMaps w (s j) (t j)) → ∃ ht : ⨆ i, nonzeroLocus (t i) = ⊤, toProj f t ht = toProj f s hs) ∧
    (∀ (T : Scheme.{0}) (g : T ⟶ Y), ∃ hg : ⨆ i, nonzeroLocus (secPull (s i) g) = ⊤,
      toProj (g ≫ f) (fun i => secPull (s i) g) hg = g ≫ toProj f s hs) ∧
    (IsClosedImmersion (toProj f s hs) ↔ VeryAmpleBy f L s) ∧
    ∀ P : PolAV (Sp R), IsProjOver P.A.hom :=
  ⟨toProj_str f s hs,
    ⟨toProj_preimage_chart f s hs, fun i j k => (secRatio_spec (s i) (s j) k).trans
      (congrArg (resG Y inf_le_left · * _) (pullRatio_toProj f s hs i j).symm)⟩,
    ⟨toProjIso f s hs, ⟨toProjIso_isGen f s hs, secMaps_toProjIso f s hs⟩,
      fun _ hw => eq_toProjIso f s hs hw.2⟩,
    fun _ _ hφ hw => eq_toProj_of_secMaps hs hφ hw,
    fun u => ⟨_, toProj_secScale hs u⟩,
    fun _ _ _ hL hB hw => ⟨iSup_nonzeroLocus_of_secMaps hs hL hB hw, toProj_eq_of_secMaps hs _ hw⟩,
    fun _ g => ⟨_, toProj_secPull hs g⟩,
    ⟨fun h => (veryAmpleBy_iff f s).2 ⟨hs, h⟩, fun h => ((veryAmpleBy_iff f s).1 h).2⟩,
    isProjOver_polAV⟩

example : VeryAmpleBy (PSpace.str R M) (O1 R M) (coord R M) :=
  (veryAmpleBy_iff _ _).2 ⟨iSup_nonzeroLocus_coord R M, by rw [toProj_coord]; infer_instance⟩

end GlobalTheory.ProjSpace

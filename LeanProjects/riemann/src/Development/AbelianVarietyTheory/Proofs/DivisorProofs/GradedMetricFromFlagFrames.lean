import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagQ
open GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagZ GlobalTheory.Cartier

section General

private theorem mem_pull_U {X Z : Scheme.{0}} (B : LB X) (f : Z ⟶ X) (c : (B.pull f).ι) (z : Z) :
    z ∈ (B.pull f).U c ↔ f z ∈ B.U (c PUnit.unit) :=
  ⟨fun h => LB.wchart_le B (fun _ : PUnit => f) c PUnit.unit h, fun h => Set.mem_iInter.2 fun _ => h⟩

private theorem le_pull_iff {X Z W : Scheme.{0}} (B : LB X) (f : Z ⟶ X) (η : W ⟶ Z) (c : (B.pull f).ι) :
    ⊤ ≤ η ⁻¹ᵁ (B.pull f).U c ↔ ⊤ ≤ (η ≫ f) ⁻¹ᵁ B.U (c PUnit.unit) :=
  ⟨fun h _ hz => (mem_pull_U B f c _).1 (h hz), fun h _ hz => (mem_pull_U B f c _).2 (h hz)⟩

private theorem le_O1_iff {X : Scheme.{0}} {C : Type} [CommRing C] {r : ℕ} {η : Sp C ⟶ X} {π : X ⟶ PSpace ℤ r}
    {v : Fin (r + 1) → C} {hv : Ideal.span (Set.range v) = ⊤}
    (e : η ≫ π = GlobalTheory.ProjSpace.pt (Int.castRingHom C) v hv) (a : PUnit → Fin (r + 1)) :
    ⊤ ≤ η ⁻¹ᵁ ((GlobalTheory.ProjSpace.O1 ℤ r).pull π).U a ↔ IsUnit (v (a PUnit.unit)) := by
  refine (le_pull_iff (GlobalTheory.ProjSpace.O1 ℤ r) π η a).trans ?_
  rw [e]
  exact GlobalTheory.Points.le_pt_preimage_chart_iff _ _ _ _

private theorem valR_O1_g {X : Scheme.{0}} {L : Type} [Field L] {r : ℕ} {η : Sp L ⟶ X} {π : X ⟶ PSpace ℤ r}
    {v : Fin (r + 1) → L} {hv : Ideal.span (Set.range v) = ⊤}
    (e : η ≫ π = GlobalTheory.ProjSpace.pt (Int.castRingHom L) v hv) (a b : PUnit → Fin (r + 1))
    (h : ⊤ ≤ η ⁻¹ᵁ (((GlobalTheory.ProjSpace.O1 ℤ r).pull π).U a ⊓ ((GlobalTheory.ProjSpace.O1 ℤ r).pull π).U b)) :
    valR η (((GlobalTheory.ProjSpace.O1 ℤ r).pull π).U a ⊓ ((GlobalTheory.ProjSpace.O1 ℤ r).pull π).U b)
      (((GlobalTheory.ProjSpace.O1 ℤ r).pull π).g a b).val = v (b PUnit.unit) / v (a PUnit.unit) := by
  have ha := (le_O1_iff e a).1 (GlobalTheory.Points.le_preimage_mono _ inf_le_left h)
  have hb := (le_O1_iff e b).1 (GlobalTheory.Points.le_preimage_mono _ inf_le_right h)
  refine (GlobalTheory.TuplePoint.valR_linComb_g η (GlobalTheory.ProjSpace.O1 ℤ r) π 1 a b h).trans ((zpow_one _).trans ?_)
  rw [e]
  have h1 : ⊤ ≤ GlobalTheory.ProjSpace.pt (Int.castRingHom L) v hv ⁻¹ᵁ
      (GlobalTheory.ProjSpace.chart ℤ r (a PUnit.unit) ⊓ GlobalTheory.ProjSpace.chart ℤ r (b PUnit.unit)) :=
    le_inf ((GlobalTheory.Points.le_pt_preimage_chart_iff _ _ _ _).2 ha) ((GlobalTheory.Points.le_pt_preimage_chart_iff _ _ _ _).2 hb)
  refine (GlobalTheory.Points.valR_res _ inf_le_left h1 (GlobalTheory.ProjSpace.ratio ℤ r (a PUnit.unit) (b PUnit.unit))).trans ?_
  refine (GlobalTheory.Points.valR_pt_ratio _ _ _ ha _).trans ?_
  rw [Ring.inverse_eq_inv, div_eq_mul_inv]

private theorem valR_tens_dual {X : Scheme.{0}} {L : Type} [Field L] (η : Sp L ⟶ X) (A B : LB X)
    (a b : A.ι × B.ι) (h : ⊤ ≤ η ⁻¹ᵁ ((A.U a.1 ⊓ B.U a.2) ⊓ (A.U b.1 ⊓ B.U b.2))) :
    valR η ((CechPic.tens A (CechPic.dual B)).U a ⊓ (CechPic.tens A (CechPic.dual B)).U b)
      ((CechPic.tens A (CechPic.dual B)).g a b).val =
      valR η (A.U a.1 ⊓ A.U b.1) (A.g a.1 b.1).val * (valR η (B.U a.2 ⊓ B.U b.2) (B.g a.2 b.2).val)⁻¹ := by
  have l₁ : (A.U a.1 ⊓ B.U a.2) ⊓ (A.U b.1 ⊓ B.U b.2) ≤ A.U a.1 ⊓ A.U b.1 := fun y h => ⟨h.1.1, h.2.1⟩
  have l₂ : (A.U a.1 ⊓ B.U a.2) ⊓ (A.U b.1 ⊓ B.U b.2) ≤ B.U a.2 ⊓ B.U b.2 := fun y h => ⟨h.1.2, h.2.2⟩
  have h₂ := GlobalTheory.Points.le_preimage_mono _ l₂ h
  refine (GlobalTheory.TuplePoint.valR_mul_unit _ h (res l₁ (A.g a.1 b.1))
    (res l₂ (B.g a.2 b.2)⁻¹)).trans (congrArg₂ (· * ·) ?_ ?_)
  · exact GlobalTheory.TuplePoint.valR_res_unit _ l₁ h _
  · exact (GlobalTheory.TuplePoint.valR_res_unit _ l₂ h _).trans (GlobalTheory.TuplePoint.valR_inv_unit _ h₂ _)

private theorem isRatSec_of_val {X Z : Scheme.{0}} [IsIntegral Z] (B : LB X) (f : Z ⟶ X)
    (s : B.ι → Z.functionFieldˣ)
    (hs : ∀ a b, ⊤ ≤ (Z.fromSpecStalk (genericPoint Z) ≫ f) ⁻¹ᵁ (B.U a ⊓ B.U b) →
      (s a : Z.functionField) =
        valR (A := Z.functionField) (Z.fromSpecStalk (genericPoint Z) ≫ f) (B.U a ⊓ B.U b) (B.g a b).val * s b) :
    IsRatSec (B.pull f) fun c => s (c PUnit.unit) := by
  intro c c' h
  have h' : ⊤ ≤ Z.fromSpecStalk (genericPoint Z) ⁻¹ᵁ ((B.pull f).U c ⊓ (B.pull f).U c') := fun w _ => by
    have : Z.fromSpecStalk (genericPoint Z) w ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := Z.fromSpecStalk (genericPoint Z) w) this (TopologicalSpace.Opens.isOpen _) h
  have e := GlobalTheory.TuplePoint.valR_linComb_g (L := Z.functionField) (Z.fromSpecStalk (genericPoint Z)) B f 1 c c' h'
  rw [zpow_one] at e
  refine (hs _ _ (le_inf ((le_pull_iff B f _ c).1 (GlobalTheory.Points.le_preimage_mono _ inf_le_left h'))
    ((le_pull_iff B f _ c').1 (GlobalTheory.Points.le_preimage_mono _ inf_le_right h')))).trans ?_
  exact congrArg (· * _) (e.symm.trans (valF_fromSpecStalk h _))

private theorem diag_minor {K : Type} [Field K] {N : ℕ} (G H : GL (Fin N) K)
    (hb : ∀ a b : Fin N, b < a → (H⁻¹ * G).1 a b = 0) (i : Fin N) (I : Rows N i.castSucc) (J : Rows N i.succ)
    (hI : minor H.1 _ I ≠ 0) (hJ : minor H.1 _ J ≠ 0) :
    minor G.1 _ I ≠ 0 ∧ minor G.1 _ J ≠ 0 ∧
      (G.1.transpose * (H.1.transpose)⁻¹) i i = minor G.1 _ J / minor G.1 _ I * (minor H.1 _ I / minor H.1 _ J) := by
  set b := (H⁻¹ * G).1 with hbdef
  have hG : G.1 = H.1 * b := by rw [hbdef, ← Units.val_mul, mul_inv_cancel_left]
  have ht : b.BlockTriangular id := fun a c h => hb a c h
  have hdet : ∏ k, b k k ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular ht]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (H⁻¹ * G).isUnit).ne_zero
  have hd (k : Fin N) : b k k ≠ 0 := Finset.prod_ne_zero_iff.1 hdet k (Finset.mem_univ _)
  have hm (l : Fin (N + 1)) (K : Rows N l) :
      minor G.1 l K = minor H.1 l K * ∏ k : Fin l, b (Fin.castLE l.is_le k) (Fin.castLE l.is_le k) := by
    rw [hG, minor_mul _ _ l (fun a c h₁ h₂ => hb a c (h₁.trans_le h₂)),
      Matrix.det_of_upperTriangular (M := b.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le))
        (fun a c h => hb _ _ h)]
    rfl
  have hp (l : Fin (N + 1)) : ∏ k : Fin l, b (Fin.castLE l.is_le k) (Fin.castLE l.is_le k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => hd _
  have hs : ∏ k : Fin i.succ, b (Fin.castLE i.succ.is_le k) (Fin.castLE i.succ.is_le k) =
      (∏ k : Fin i.castSucc, b (Fin.castLE i.castSucc.is_le k) (Fin.castLE i.castSucc.is_le k)) * b i i :=
    Fin.prod_univ_castSucc (n := i) _
  have he : G.1.transpose * (H.1.transpose)⁻¹ = b.transpose := by
    rw [hG, Matrix.transpose_mul, Matrix.mul_nonsing_inv_cancel_right]
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 H.isUnit
  refine ⟨by rw [hm]; exact mul_ne_zero hI (hp _), by rw [hm]; exact mul_ne_zero hJ (hp _), ?_⟩
  have := hp i.castSucc
  rw [he, hm _ I, hm _ J, hs, Matrix.transpose_apply]
  field_simp

end General

section Charts

variable {ι : Type} [Fintype ι] {N : ℕ}

private theorem flagPt_π {C : Type} [CommRing C] (g : ι → GL (Fin N) C) (τ : ι) (l : Fin (N + 1)) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ plEmb Prod.fst Prod.snd ≫ Pi.π _ (τ, l) =
      GlobalTheory.ProjSpace.pt (Int.castRingHom C) (plVec (g τ).1 l) (span_plVec _ _) :=
  (flagPt_plEmb_assoc (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g (Pi.π _ (τ, l))).trans (plPt_π _ _ g (τ, l))

private theorem le_gr_iff {C : Type} [CommRing C] (g : ι → GL (Fin N) C) (x : ι × Fin N) (a : (grLine x).B.ι) :
    ⊤ ≤ flagPt Prod.fst Prod.snd g ⁻¹ᵁ (grLine x).B.U a ↔
      IsUnit (plVec (g x.1).1 x.2.castSucc (a.1 PUnit.unit)) ∧ IsUnit (plVec (g x.1).1 x.2.succ (a.2 PUnit.unit)) :=
  Iff.trans ⟨fun h => ⟨fun _ hz => (h hz).1, fun _ hz => (h hz).2⟩, fun h _ hz => ⟨h.1 hz, h.2 hz⟩⟩
    (and_congr (le_O1_iff (flagPt_π g x.1 x.2.castSucc) a.1) (le_O1_iff (flagPt_π g x.1 x.2.succ) a.2))

private theorem valR_gr_g {L : Type} [Field L] (g : ι → GL (Fin N) L) (x : ι × Fin N) (a b : (grLine x).B.ι)
    (h : ⊤ ≤ flagPt Prod.fst Prod.snd g ⁻¹ᵁ ((grLine x).B.U a ⊓ (grLine x).B.U b)) :
    valR (flagPt Prod.fst Prod.snd g) ((grLine x).B.U a ⊓ (grLine x).B.U b) ((grLine x).B.g a b).val =
      plVec (g x.1).1 x.2.castSucc (b.1 PUnit.unit) / plVec (g x.1).1 x.2.castSucc (a.1 PUnit.unit) *
        (plVec (g x.1).1 x.2.succ (b.2 PUnit.unit) / plVec (g x.1).1 x.2.succ (a.2 PUnit.unit))⁻¹ :=
  (valR_tens_dual _ (flDet x.1 x.2.castSucc).B (flDet x.1 x.2.succ).B a b h).trans
    (congrArg₂ (fun s t => s * t⁻¹)
      (valR_O1_g (flagPt_π g x.1 x.2.castSucc) a.1 b.1 fun _ hz => ⟨(h hz).1.1, (h hz).2.1⟩)
      (valR_O1_g (flagPt_π g x.1 x.2.succ) a.2 b.2 fun _ hz => ⟨(h hz).1.2, (h hz).2.2⟩))

private def colRat {L : Type} [Field L] (g : ι → GL (Fin N) L) (x : ι × Fin N) (a : (grLine x).B.ι) : Lˣ :=
  if h : plVec (g x.1).1 x.2.castSucc (a.1 PUnit.unit) ≠ 0 ∧ plVec (g x.1).1 x.2.succ (a.2 PUnit.unit) ≠ 0 then
    Units.mk0 _ (div_ne_zero h.2 h.1) else 1

private theorem val_colRat {L : Type} [Field L] (g : ι → GL (Fin N) L) (x : ι × Fin N) (a : (grLine x).B.ι)
    (h₁ : plVec (g x.1).1 x.2.castSucc (a.1 PUnit.unit) ≠ 0) (h₂ : plVec (g x.1).1 x.2.succ (a.2 PUnit.unit) ≠ 0) :
    (colRat g x a : L) =
      plVec (g x.1).1 x.2.succ (a.2 PUnit.unit) / plVec (g x.1).1 x.2.castSucc (a.1 PUnit.unit) := by
  rw [colRat, dif_pos ⟨h₁, h₂⟩, Units.val_mk0]

private theorem colRat_trans {L : Type} [Field L] (g : ι → GL (Fin N) L) (x : ι × Fin N) (a b : (grLine x).B.ι)
    (h : ⊤ ≤ flagPt Prod.fst Prod.snd g ⁻¹ᵁ ((grLine x).B.U a ⊓ (grLine x).B.U b)) :
    (colRat g x a : L) =
      valR (flagPt Prod.fst Prod.snd g) ((grLine x).B.U a ⊓ (grLine x).B.U b) ((grLine x).B.g a b).val *
        colRat g x b := by
  obtain ⟨a₁, a₂⟩ := (le_gr_iff g x a).1 (GlobalTheory.Points.le_preimage_mono _ inf_le_left h)
  obtain ⟨b₁, b₂⟩ := (le_gr_iff g x b).1 (GlobalTheory.Points.le_preimage_mono _ inf_le_right h)
  have a₁ := a₁.ne_zero
  have a₂ := a₂.ne_zero
  have b₁ := b₁.ne_zero
  have b₂ := b₂.ne_zero
  rw [valR_gr_g g x a b h, val_colRat g x a a₁ a₂, val_colRat g x b b₁ b₂]
  field_simp

variable {Y : Var ℚ}

private theorem isRatSec_colRat (j : Y.X ⟶ Fl ι N) (x : ι × Fin N) :
    IsRatSec ((grLine x).B.pull j) fun c => colRat (genMat j) x (c PUnit.unit) := by
  refine isRatSec_of_val (grLine x).B j (colRat (genMat j) x) ?_
  have e : Y.X.fromSpecStalk (genericPoint Y.X) ≫ j = flagPt Prod.fst Prod.snd (genMat j) := flagPt_genMat j
  have h := colRat_trans (genMat j) x
  rw [← e] at h
  exact h

private theorem flagPt_genMat_eq (j : Y.X ⟶ Fl ι N) (y : Y.X) (g : ι → GL (Fin N) (Y.X.presheaf.stalk y))
    (hg : Y.X.fromSpecStalk y ≫ j = flagPt Prod.fst Prod.snd g) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd
        (fun τ => Matrix.GeneralLinearGroup.map (algebraMap (Y.X.presheaf.stalk y) Y.Fn) (g τ)) =
      flagPt Prod.fst Prod.snd (genMat j) := by
  rw [← flagPt_genMat, ← spMap_flagPt, ← hg, ← Category.assoc]
  exact congrArg (· ≫ j) (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y))

private theorem isFrame_local (j : Y.X ⟶ Fl ι N) (y : Y.X) (g : ι → GL (Fin N) (Y.X.presheaf.stalk y))
    (hg : Y.X.fromSpecStalk y ≫ j = flagPt Prod.fst Prod.snd g) :
    IsFrame j y fun τ =>
      (Matrix.GeneralLinearGroup.map (algebraMap (Y.X.presheaf.stalk y) Y.Fn) (g τ)).1.transpose := by
  have hb := (flagPt_eq_iff_below ι _ N Prod.fst Prod.snd Y.Fn _ _).1 (flagPt_genMat_eq j y g hg).symm
  set φ : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap _ _ with hφ
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · have hu := (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit
    have hd : (Matrix.GeneralLinearGroup.map φ (g τ)).1.transpose.det = φ (g τ).1.det := by
      rw [Matrix.det_transpose]; exact (φ.map_det _).symm
    refine ⟨fun a b => mem_O_ratOf.2 ⟨(g τ).1 b a, rfl⟩, ?_, ?_, fun a b ha _ => absurd ha (Nat.not_lt_zero _)⟩
    · exact fun h => (hu.map φ).ne_zero (hd.symm.trans h)
    · refine mem_O_ratOf.2 ⟨(hu.unit⁻¹ : (Y.X.presheaf.stalk y)ˣ), ?_⟩
      refine Eq.trans ?_ (congrArg (·⁻¹) hd).symm
      exact map_units_inv φ hu.unit
  · have he : (Matrix.GeneralLinearGroup.map φ (g τ)).1.transpose * ((genMat j τ).1.transpose)⁻¹ =
        ((genMat j τ)⁻¹ * Matrix.GeneralLinearGroup.map φ (g τ)).1.transpose := by
      rw [Units.val_mul, Matrix.transpose_mul, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]
    refine ⟨fun _ _ => trivial, ?_, trivial, fun a b _ hab => ?_⟩
    · refine fun h => ((Matrix.isUnit_iff_isUnit_det _).1
        ((genMat j τ)⁻¹ * Matrix.GeneralLinearGroup.map φ (g τ)).isUnit).ne_zero ?_
      rw [← Matrix.det_transpose, ← he]
      exact h
    · exact (congrFun (congrFun he a) b).trans
        (hb τ b a ⟨(τ, ⟨b, Nat.lt_succ_of_lt b.isLt⟩), rfl, hab, le_refl _⟩)

end Charts

end GlobalTheory.FlagQ

open GlobalTheory.FlagQ GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagZ GlobalTheory.Cartier in
theorem _root_.GlobalTheory.T.graded_metric_from_flag_frames : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) → ∀ (E' : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf Y) (fun _ : ι => N) (fun _ => N)), (∀ y A', A' ∈ E'.S y ↔ GlobalTheory.FlagQ.IsFrame j y A') → ∃ gr : ι × Fin N → Y.Dv, (∀ x, ∃ r, GlobalTheory.Cartier.Presents (gr x) ((GlobalTheory.FlagZ.grLine x).B.pull j) r) ∧ GlobalTheory.GoodMetric.IsGraded E' (fun x => gr (x.1, x.2)) := by
  intro ι _ N Y j _ E' hE
  have hL (x : ι × Fin N) : ((grLine x).B.pull j).IsLB := LB.isLB_pull (grLine x).isLB j
  have hr (x : ι × Fin N) := isRatSec_colRat j x
  have hdet (τ : ι) : (genFrame j τ).det ≠ 0 := by
    show ((genMat j τ).1.transpose).det ≠ 0
    rw [Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (genMat j τ).isUnit).ne_zero
  refine ⟨fun x => divOfRatSec (hL x) (hr x), fun x => ⟨_, presents_divOfRatSec (hL x) (hr x)⟩, genFrame j, ?_, ?_⟩
  · refine (hE _ _).2 ⟨fun τ => ⟨fun a b => mem_O_ratOf.2 (regAt_genericPoint _), hdet τ,
      mem_O_ratOf.2 (regAt_genericPoint _), fun a b ha _ => absurd ha (Nat.not_lt_zero _)⟩, ?_⟩
    rw [Mat.mul_inv hdet]
    exact Par.one
  · intro y x
    have hloc : IsLocalRing (Y.X.presheaf.stalk y) := Y.X.toLocallyRingedSpace.isLocalRing y
    obtain ⟨g, hg⟩ := @exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd
      (Y.X.presheaf.stalk y) _ hloc (Y.X.fromSpecStalk y ≫ j)
    have hb := (flagPt_eq_iff_below ι _ N Prod.fst Prod.snd Y.Fn _ _).1 (flagPt_genMat_eq j y g hg)
    have hF := isFrame_local j y g hg
    set φ : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap _ _ with hφ
    set g' : ι → GL (Fin N) Y.Fn := fun τ => Matrix.GeneralLinearGroup.map φ (g τ) with hg'
    have hex (l : Fin (N + 1)) : ∃ c, IsUnit (plVec (g x.1).1 l c) := by
      by_contra h
      push_neg at h
      have hle : Ideal.span (Set.range (plVec (g x.1).1 l)) ≤ IsLocalRing.maximalIdeal _ :=
        Ideal.span_le.2 (Set.range_subset_iff.2 fun a => (IsLocalRing.mem_maximalIdeal _).2 (h _))
      rw [span_plVec] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
    obtain ⟨I, hI⟩ := hex (Fin.castSucc x.2)
    obtain ⟨J, hJ⟩ := hex (Fin.succ x.2)
    have hmap (l : Fin (N + 1)) (c) : plVec (g' x.1).1 l c = φ (plVec (g x.1).1 l c) := minor_map φ _ _ _
    have hI' : plVec (g' x.1).1 _ I ≠ 0 := by rw [hmap]; exact (hI.map φ).ne_zero
    have hJ' : plVec (g' x.1).1 _ J ≠ 0 := by rw [hmap]; exact (hJ.map φ).ne_zero
    obtain ⟨hGI, hGJ, hdiag⟩ := diag_minor (genMat j x.1) (g' x.1)
      (fun a b hba => hb x.1 a b ⟨(x.1, ⟨a, Nat.lt_succ_of_lt a.isLt⟩), rfl, hba, le_refl _⟩) x.2 _ _ hI' hJ'
    have hu : UnitAt y (plVec (g' x.1).1 _ I / plVec (g' x.1).1 _ J) := by
      refine ⟨((hI.unit * hJ.unit⁻¹ : (Y.X.presheaf.stalk y)ˣ) : Y.X.presheaf.stalk y), Units.isUnit _, ?_⟩
      rw [Units.val_mul, map_mul, map_units_inv, IsUnit.unit_spec, IsUnit.unit_spec, hmap, hmap, div_eq_mul_inv]
    let a : (grLine ((x.1, x.2) : ι × Fin N)).B.ι := (fun _ => I, fun _ => J)
    have hc : y ∈ ((grLine ((x.1, x.2) : ι × Fin N)).B.pull j).U (fun _ => a) := by
      have h₁ := (le_gr_iff g (x.1, x.2) a).2 ⟨hI, hJ⟩
      rw [← hg] at h₁
      have h₂ := (le_pull_iff _ j (Y.X.fromSpecStalk y) (fun _ => a)).2 h₁
        (x := IsLocalRing.closedPoint (Y.X.presheaf.stalk y)) trivial
      have h₃ : Y.X.fromSpecStalk y (IsLocalRing.closedPoint (Y.X.presheaf.stalk y)) ∈
          ((grLine ((x.1, x.2) : ι × Fin N)).B.pull j).U (fun _ => a) := h₂
      rwa [Scheme.fromSpecStalk_closedPoint] at h₃
    have he := (presents_divOfRatSec (hL (x.1, x.2)) (hr (x.1, x.2))).isEqn _ y hc
    refine ⟨fun τ => (g' τ).1.transpose, (hE y _).2 hF,
      colRat (genMat j) (x.1, x.2) a * Units.mk0 _ (div_ne_zero hI' hJ'), ?_, ?_⟩
    · refine hdiag.trans ?_
      rw [Units.val_mul, val_colRat (genMat j) (x.1, x.2) a hGI hGJ, Units.val_mk0]
      rfl
    · refine he.iff_unitAt.2 ?_
      rw [Units.val_mul, mul_div_cancel_left₀ _ (Units.ne_zero _), Units.val_mk0]
      exact hu

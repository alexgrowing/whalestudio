import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

noncomputable section
namespace GlobalTheory.FlagZ.TautPull
open GlobalTheory.VB
open GlobalTheory.QCoh (appLinear appLinear_apply pullbackSections)
open GlobalTheory.Twist (app_resM resM_resM resM_smul resM_self)

private theorem glue_frame {X : Scheme.{0}} {P Q : X.Modules} (m : P ⟶ Q) {l : ℕ} (c : Fin l → Γ(Q, ⊤))
    (hc : ∀ V : X.Opens, LinearIndependent Γ(X, V) fun j => resM Q (le_top : V ≤ ⊤) (c j))
    (H : ∀ y : X, ∃ (W : X.Opens) (t : Fin l → Γ(P, W)), y ∈ W ∧ VB.IsFrame t ∧
      ∀ j, m.app W (t j) = resM Q (le_top : W ≤ ⊤) (c j)) :
    ∃ s : Fin l → Γ(P, ⊤), VB.IsFrame s ∧ ∀ j, m.app ⊤ (s j) = c j := by
  choose W t hy ht hm using H
  have hres (y : X) (V : X.Opens) (h : V ≤ W y) (j : Fin l) :
      m.app V (resM P h (t y j)) = resM Q (le_top : V ≤ ⊤) (c j) := by
    rw [app_resM, hm, resM_resM]
  have hinj (y : X) (V : X.Opens) (h : V ≤ W y) : Function.Injective (m.app V) := by
    rw [← show ⇑(appLinear m V) = ⇑(m.app V) from rfl, injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨a, rfl⟩ := (ht y V h).2 s
    rw [Fintype.linearCombination_apply, map_sum] at hs
    simp only [map_smul, appLinear_apply, hres] at hs
    rw [show a = 0 from funext (Fintype.linearIndependent_iff.1 (hc V) a hs), map_zero]
  have hcov : (⊤ : X.Opens) ≤ iSup W := fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  choose s hs using fun j => GlobalTheory.Twist.exists_sec_of_cover (F := P) W (fun _ => le_top) hcov (fun y => t y j)
    fun y z => hinj y _ inf_le_left ((hres y _ _ j).trans (hres z _ _ j).symm)
  refine ⟨s, isFrame_of_forall_exists fun V h x hx => ⟨V ⊓ W x, inf_le_left, ⟨hx, hy x⟩, ?_⟩, fun j => ?_⟩
  · have := ht x (V ⊓ W x) inf_le_right
    simp only [← hs, resM_resM] at this
    exact this
  · refine GlobalTheory.Twist.sec_ext_of_cover W (fun _ => le_top) hcov fun y => ?_
    rw [← app_resM, hs, hm]

private theorem isFrame_colSec (N : ℕ) (A : Type) [CommRing A] (x : Sp A ⟶ Sp ℤ) (g : GL (Fin N) A) :
    VB.IsFrame (GlobalTheory.FlagZ.Taut.colSec x g.1) :=
  isFrame_sum_smul_of_isUnit ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback x)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.mapMatrix g.1) (g.isUnit.map _)

private theorem exists_isFrame_sub {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ}
    (P : VB.Sub F) (c : Fin N → Γ(F, U)) (hc : VB.IsFrame c) (l : ℕ) (hl : l ≤ N)
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
    ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e ∧ ∀ j, P.incl.app U (e j) = c (Fin.castLE hl j) := by
  classical
  have hmem (k : Fin l) : c (Fin.castLE hl k) ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (Fin.castLE hl k) 1)).2 fun j hj => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      simp at hj
      omega
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  let e : Fin l → Γ(P.toMod, U) := fun k => P.mkSec _ (hmem k)
  have hincl (V : X.Opens) (h : V ≤ U) (b : Fin l → Γ(X, V)) :
      P.incl.app V (Fintype.linearCombination Γ(X, V) (fun k => resM P.toMod h (e k)) b) =
        ∑ k, b k • resM F h (c (Fin.castLE hl k)) := by
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, appLinear_apply, app_resM]
    rfl
  refine ⟨e, fun V h => ⟨fun b b' hbb => ?_, fun s => ?_⟩, fun _ => rfl⟩
  · have h1 := congrArg (P.incl.app V) hbb
    rw [hincl, hincl] at h1
    exact funext (Fintype.linearIndependent_iffₛ.1
      (((isFrame_iff.1 hc V h).1).comp _ (Fin.castLE_injective hl)) b b' h1)
  · obtain ⟨a, ha⟩ := (hc V h).2 (P.incl.app V s)
    rw [Fintype.linearCombination_apply] at ha
    have hz := (hP V h a).1 (ha ▸ P.incl_app_mem s)
    refine ⟨fun k => a (Fin.castLE hl k), P.incl_app_injective V ?_⟩
    rw [hincl, ← ha]
    exact sum_castLE_eq hl (fun j => a j • resM F h (c j)) fun j hj => by rw [hz j hj, zero_smul]

private theorem exists_frame_cell (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) :
    ∃ e : Fin l → Γ(F ι N τ l, cellOpen ι N w), VB.IsFrame e ∧
      ∀ j, (sub ι N τ l).incl.app _ (e j) = cellCol ι N w τ (Fin.castLE l.is_le j) :=
  exists_isFrame_sub (sub ι N τ l) _ (isFrame_cellCol ι N w τ) l l.is_le (mem_sub_iff_cellCol ι N τ l w)

set_option backward.isDefEq.respectTransparency false in

private theorem pull_comb {T Y Z : Scheme.{0}} (x : T ⟶ Y) (q : Y ⟶ Z) (E : Z.Modules) {F : Y.Modules}
    (i : F ⟶ (Scheme.Modules.pullback q).obj E) {μ : Type} [Fintype μ] (e : μ → Γ(E, ⊤)) {U : Y.Opens}
    (s : Γ(F, U)) (a : μ → Γ(Y, U)) (h₁ : U ≤ q ⁻¹ᵁ ⊤) (h₂ : x ⁻¹ᵁ U ≤ (x ≫ q) ⁻¹ᵁ ⊤)
    (hs : i.app U s = ∑ m, a m • pullbackSections q E h₁ (e m)) :
    ((Scheme.Modules.pullback x).map i ≫ (Scheme.Modules.pullbackComp x q).hom.app E).app (x ⁻¹ᵁ U)
        (pullbackSections x F le_rfl s) =
      ∑ m, x.appLE U (x ⁻¹ᵁ U) le_rfl (a m) • pullbackSections (x ≫ q) E h₂ (e m) := by
  have h3 := QCoh.pullback_map_app_pullbackSections x i (le_refl (x ⁻¹ᵁ U)) s
  refine (congrArg (((Scheme.Modules.pullbackComp x q).hom.app E).app _) h3).trans ?_
  rw [hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul,
    ← Vert.DivPull.pullbackComp_inv_app x q E h₁ le_rfl h₂]
  congr 1
  exact congr(($((Scheme.Modules.pullbackComp x q).inv_hom_id_app E)).app _ _)

set_option backward.isDefEq.respectTransparency false in

private theorem pull_incl_cellCol (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) {T : Scheme.{0}} (x : T ⟶ Fl ι N) (s : Γ(F ι N τ l, cellOpen ι N w)) (k : Fin N)
    (hs : (sub ι N τ l).incl.app _ s = cellCol ι N w τ k) :
    ((Scheme.Modules.pullback x).map (incl ι N τ l) ≫
        (Scheme.Modules.pullbackComp x (flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N)).app (x ⁻¹ᵁ cellOpen ι N w)
        (QCoh.pullbackSections x (F ι N τ l) le_rfl s) =
      ∑ i, x.appLE (cellOpen ι N w) (x ⁻¹ᵁ cellOpen ι N w) le_rfl
          (cellRing ι N w ((cellGL Prod.fst Prod.snd w τ).1 i k)) •
        resM _ le_top (QCoh.pullbackSections (x ≫ flStr ι N) (GlobalTheory.FlagZ.Taut.stdE N) (by simp)
          (VB.freeFrame (Sp ℤ) (Fin N) i)) := by
  refine (pull_comb x (flStr ι N) (GlobalTheory.FlagZ.Taut.stdE N) (incl ι N τ l) (VB.freeFrame (Sp ℤ) (Fin N)) s
    (fun i => cellRing ι N w ((cellGL Prod.fst Prod.snd w τ).1 i k)) le_top le_top ?_).trans
    (Finset.sum_congr rfl fun i _ => congrArg _ (QCoh.res_pullbackSections _ _ _ _ _).symm)
  refine (congrArg ((freeIso ι N).inv.app _) hs).trans ?_
  rw [cellCol, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, app_resM]
  congr 1
  have h1 : (freeIso ι N).hom.app ⊤ _ = _ := IsFrame.iso_hom_app
    ((VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (flStr ι N)) (VB.isFrame_freeFrame _ (Fin N)) i
  rw [← h1]
  refine Eq.trans (congrArg _ ?_) (QCoh.res_pullbackSections (flStr ι N) _ (U := ⊤) le_top _ _)
  exact congr(($((freeIso ι N).hom_inv_id)).app ⊤ _)

private theorem spMap_cellRing_cell (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N))
    (hU : IsAffineOpen (cellOpen ι N w)) :
    spMap (cellRing ι N w) ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = hU.fromSpec := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) hU
    (isAffineOpen_top _) (Scheme.Hom.preimage_image_eq _ ⊤).ge
  have e₀ : ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).hom =
      (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appLE (cellOpen ι N w) ⊤
        (Scheme.Hom.preimage_image_eq _ ⊤).ge :=
    Scheme.Hom.appIso_hom' _ _
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← e₀] at h
  have e : spMap (cellRing ι N w) = Spec.map ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).inv := by
    exact Spec.map_comp _ _
  rw [e]
  erw [Category.assoc, ← h]
  erw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

private theorem spMap_res (A : Type) [CommRing A] (W : (Sp A).Opens) (hW : IsAffineOpen W) :
    spMap ((resG (Sp A) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = hW.fromSpec := by
  have h := IsAffineOpen.map_fromSpec (isAffineOpen_top (Sp A)) hW (homOfLE le_top).op
  rw [IsAffineOpen.fromSpec_top] at h
  erw [Scheme.isoSpec_Spec_inv] at h
  rw [← h]
  exact Spec.map_comp _ _

private theorem exists_upper_cell (ι : Type) [Fintype ι] (N : ℕ) (A : Type) [CommRing A] (g : ι → GL (Fin N) A) (a : ι)
    (w : ι → Equiv.Perm (Fin N)) (y : Sp A)
    (hy : y ∈ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w) :
    ∃ (W : (Sp A).Opens) (hW : W ≤ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w)
      (B : Matrix (Fin N) (Fin N) Γ(Sp A, W)), y ∈ W ∧ (∀ i j : Fin N, j < i → B i j = 0) ∧ IsUnit B.det ∧
      ∀ i j, resG (Sp A) (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((g a).1 i j)) =
        ∑ k, resG (Sp A) hW ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE (cellOpen ι N w)
          (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w) le_rfl
          (cellRing ι N w ((cellGL Prod.fst Prod.snd w a).1 i k))) * B k j := by
  have hU : IsAffineOpen (cellOpen ι N w) :=
    (isAffineOpen_top (Sp (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).image_of_isOpenImmersion _
  obtain ⟨W, hWa, hyW, hW⟩ := exists_isAffineOpen_mem_and_subset hy
  have hW : W ≤ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w := hW
  set x := flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g with hx
  let ψ : A →+* Γ(Sp A, W) := (resG (Sp A) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let φ : CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd →+* Γ(Sp A, W) :=
    (x.appLE _ W hW).hom.comp (cellRing ι N w)
  have key : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd
      (fun τ => Matrix.GeneralLinearGroup.map φ (cellGL Prod.fst Prod.snd w τ)) =
      flagPt Prod.fst Prod.snd (fun τ => Matrix.GeneralLinearGroup.map ψ (g τ)) := by
    rw [← spMap_flagPt, ← spMap_flagPt, ← hx, ← cell, spMap_res A W hWa,
      ← IsAffineOpen.SpecMap_appLE_fromSpec x hU hWa hW, ← spMap_cellRing_cell ι N w hU]
    rw [spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  have hB := (flagPt_eq_iff_below _ _ _ _ _ _ _ _).1 key a
  refine ⟨W, hW, ((Matrix.GeneralLinearGroup.map φ (cellGL Prod.fst Prod.snd w a))⁻¹ *
    Matrix.GeneralLinearGroup.map ψ (g a)).1, hyW, fun i j h => hB i j ⟨(a, i.castSucc), rfl, h, le_rfl⟩,
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _), fun i j => ?_⟩
  have e := congrArg (fun m : GL (Fin N) Γ(Sp A, W) => m.1 i j) (mul_inv_cancel_left
    (Matrix.GeneralLinearGroup.map φ (cellGL Prod.fst Prod.snd w a)) (Matrix.GeneralLinearGroup.map ψ (g a)))
  refine e.symm.trans ?_
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (· * _) (LB.resG_appLE x le_rfl hW _).symm

private theorem isUnit_det_castLE {R : Type} [CommRing R] {N : ℕ} (B : Matrix (Fin N) (Fin N) R)
    (hB : ∀ i j : Fin N, j < i → B i j = 0) (hdet : IsUnit B.det) (l : ℕ) (hl : l ≤ N) :
    IsUnit (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have ht : B.BlockTriangular id := fun i j h => hB i j h
  have ht' : (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := fun i j h => hB _ _ h
  rw [Matrix.det_of_upperTriangular ht] at hdet
  rw [Matrix.det_of_upperTriangular ht']
  exact IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.1 hdet (Fin.castLE hl i)

end GlobalTheory.FlagZ.TautPull

open GlobalTheory.VB GlobalTheory.FlagZ.TautPull in
theorem _root_.GlobalTheory.T.pullback_flag_sections_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (A : Type) [CommRing A] (g : ι → GL (Fin N) A) (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).obj (F ι N a l), ⊤),
      VB.IsFrame s ∧ ∀ j, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map (incl ι N a l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app
          (GlobalTheory.FlagZ.Taut.stdE N)).app ⊤ (s j) =
        GlobalTheory.FlagZ.Taut.colSec (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j) := by
  intro ι _ N A _ g a l
  haveI : (F ι N a l).IsQuasicoherent := (GlobalTheory.T.tautological_subbundle_rank ι N a l).1.isQuasicoherent
  refine glue_frame _ _ (fun V => ?_) (fun y => ?_)
  · exact ((isFrame_iff.1 (isFrame_colSec N A _ (g a)) V le_top).1).comp _ (Fin.castLE_injective _)
  · obtain ⟨w, hw⟩ := GlobalTheory.FlagZ.exists_mem_range_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd
      (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g y)
    have hy : y ∈ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ cellOpen ι N w := (mem_cellOpen ι N).2 hw
    obtain ⟨W, hW, B, hyW, hBt, hBd, hB⟩ := exists_upper_cell ι N A g a w y hy
    obtain ⟨e, he, hinc⟩ := exists_frame_cell ι N a l w
    have ht0 := he.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)
    refine ⟨W, fun j => ∑ k, B.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) k j • resM _ hW
      (QCoh.pullbackSections (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (F ι N a l) le_rfl (e k)), hyW,
      isFrame_sum_smul_of_isUnit (ht0.res hW) _
        ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_castLE B hBt hBd l l.is_le)), fun j => ?_⟩
    set q : Fin N → Γ((Scheme.Modules.pullback ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ≫ flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N), ⊤) := fun i =>
      QCoh.pullbackSections ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ≫ flStr ι N) (GlobalTheory.FlagZ.Taut.stdE N) (by simp) (VB.freeFrame (Sp ℤ) (Fin N) i) with hq
    have h1 : ∀ k : Fin l, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map (incl ι N a l) ≫
        (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N)).app W
          (resM _ hW (QCoh.pullbackSections (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (F ι N a l) le_rfl (e k))) =
        ∑ i, resG (Sp A) hW ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE (cellOpen ι N w) ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ⁻¹ᵁ cellOpen ι N w) le_rfl
          (cellRing ι N w ((cellGL Prod.fst Prod.snd w a).1 i (Fin.castLE l.is_le k)))) •
            resM _ (le_top : W ≤ ⊤) (q i) := by
      intro k
      rw [GlobalTheory.Twist.app_resM, pull_incl_cellCol ι N a l w (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (e k) _ (hinc k), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [GlobalTheory.Twist.resM_smul, GlobalTheory.Twist.resM_resM]
    have h2 : resM _ (le_top : W ≤ ⊤) (GlobalTheory.FlagZ.Taut.colSec ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j)) =
        ∑ i, resG (Sp A) (le_top : W ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((g a).1 i (Fin.castLE l.is_le j))) •
          resM _ (le_top : W ≤ ⊤) (q i) := by
      rw [GlobalTheory.FlagZ.Taut.colSec, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [GlobalTheory.Twist.resM_smul]
    rw [h2, map_sum]
    simp_rw [Scheme.Modules.Hom.app_smul, h1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, hB]
    congr 1
    refine Fintype.sum_of_injective (Fin.castLE l.is_le) (Fin.castLE_injective _) _ _ (fun k hk => ?_) fun k => mul_comm _ _
    have hk' : (l : ℕ) ≤ (k : ℕ) := not_lt.1 fun h => hk ⟨⟨k, h⟩, rfl⟩
    rw [hBt k _ (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.2 hk')), mul_zero]

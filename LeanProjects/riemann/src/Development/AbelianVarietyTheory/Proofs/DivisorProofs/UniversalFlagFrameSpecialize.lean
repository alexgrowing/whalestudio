import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTautologicalFrame
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

set_option autoImplicit false
noncomputable section
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)

namespace GlobalTheory.FlagZ.Univ

private theorem exists_frame_of_local {T : Scheme.{0}} {F' G' : T.Modules} (φ : F' ⟶ G') {n : ℕ}
    (c : Fin n → Γ(G', ⊤))
    (H : ∀ y : T, ∃ (V : T.Opens) (s : Fin n → Γ(F', V)), y ∈ V ∧ GlobalTheory.VB.IsFrame s ∧
      (∀ j, φ.app V (s j) = resM G' le_top (c j)) ∧ ∀ W : T.Opens, W ≤ V → Function.Injective (φ.app W)) :
    ∃ s : Fin n → Γ(F', ⊤), GlobalTheory.VB.IsFrame s ∧ ∀ j, φ.app ⊤ (s j) = c j := by
  choose V s hy hs hφ hinj using H
  have hc : (⊤ : T.Opens) ≤ iSup V := fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
  choose t ht using fun j => exists_sec_of_cover (F := F') V (fun _ => le_top) hc (fun y => s y j)
    fun y z => hinj y _ inf_le_left (by rw [app_resM, app_resM, hφ, hφ, resM_resM, resM_resM])
  refine ⟨t, GlobalTheory.VB.isFrame_of_forall_exists fun W h y hyW => ⟨W ⊓ V y, inf_le_left, ⟨hyW, hy y⟩, ?_⟩,
    fun j => sec_ext_of_cover V (fun _ => le_top) hc fun y => ?_⟩
  · have := hs y (W ⊓ V y) inf_le_right
    simp only [← ht, resM_resM] at this
    exact this
  · rw [← app_resM, ht, hφ]

private theorem resM_colSec {N : ℕ} {A : Type} [CommRing A] (x : Sp A ⟶ Sp ℤ) (G : Matrix (Fin N) (Fin N) A)
    (V : (Sp A).Opens) (j : Fin N) :
    resM _ (le_top : V ≤ ⊤) (GlobalTheory.FlagZ.Taut.colSec x G j) =
      GlobalTheory.FlagZ.Loc.colSecOn x V
        (G.map ((resG (Sp A) (le_top : V ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) j := by
  unfold GlobalTheory.FlagZ.Taut.colSec GlobalTheory.FlagZ.Loc.colSecOn
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [resM_smul]
  congr 1
  exact GlobalTheory.QCoh.res_pullbackSections _ _ _ _ _

private theorem isFrame_colSecOn {T : Scheme.{0}} (x : T ⟶ Sp ℤ) {N : ℕ} (V : T.Opens)
    (C : GL (Fin N) Γ(T, V)) : GlobalTheory.VB.IsFrame (Loc.colSecOn x V C.1) := by
  haveI : (Taut.stdE N).IsQuasicoherent := (GlobalTheory.VB.isVB_freeModule_fin (Sp ℤ) N).isQuasicoherent
  have h := (GlobalTheory.VB.IsFrame.pullback (F := Taut.stdE N) (GlobalTheory.VB.isFrame_freeFrame (Sp ℤ) (Fin N)) x).res
    (le_top : V ≤ x ⁻¹ᵁ ⊤)
  have h' : GlobalTheory.VB.IsFrame fun i => GlobalTheory.QCoh.pullbackSections x (Taut.stdE N) (le_top : V ≤ x ⁻¹ᵁ ⊤)
      (GlobalTheory.VB.freeFrame (Sp ℤ) (Fin N) i) := by
    convert h using 2
    exact (GlobalTheory.QCoh.res_pullbackSections _ _ _ _ _).symm
  exact isFrame_sum_smul_of_isUnit h' C.1 C.isUnit

private theorem exists_frame_mul {T : Scheme.{0}} (x : T ⟶ Sp ℤ) {N : ℕ} {F' : T.Modules}
    (φ : F' ⟶ (Scheme.Modules.pullback x).obj (Taut.stdE N)) (V : T.Opens) (l : Fin (N + 1))
    (e : Fin l → Γ(F', V)) (C b : GL (Fin N) Γ(T, V))
    (he : GlobalTheory.VB.IsFrame e) (hφ : ∀ k, φ.app V (e k) = Loc.colSecOn x V C.1 (Fin.castLE l.is_le k))
    (hb : ∀ i j : Fin N, j < i → b.1 i j = 0) :
    (∀ W : T.Opens, W ≤ V → Function.Injective (φ.app W)) ∧
      ∃ s : Fin l → Γ(F', V), GlobalTheory.VB.IsFrame s ∧
        ∀ j, φ.app V (s j) = Loc.colSecOn x V (C.1 * b.1) (Fin.castLE l.is_le j) := by
  have hb' : ∀ i j : Fin N, (j : ℕ) < l → (l : ℕ) ≤ i → b.1 i j = 0 := fun i j h₁ h₂ => hb i j (h₁.trans_le h₂)
  refine ⟨fun W hW => ?_, fun j => ∑ k, b.1.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le) k j • e k,
    isFrame_sum_smul_of_isUnit he _ ?_, fun j => ?_⟩
  · refine (injective_iff_map_eq_zero (φ.app W).hom).2 fun s hs => ?_
    obtain ⟨a, rfl⟩ := (he W hW).2 s
    have li := (GlobalTheory.VB.isFrame_iff.1 (isFrame_colSecOn x V C) W hW).1.comp _ (Fin.castLE_injective l.is_le)
    have ha := Fintype.linearIndependent_iff.1 li a (by
      rw [← hs, Fintype.linearCombination_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Scheme.Modules.Hom.app_smul, app_resM, hφ]
      rfl)
    rw [show a = 0 from funext ha, map_zero]
  · rw [Matrix.isUnit_iff_isUnit_det]
    refine Ideal.span_singleton_eq_top.1 (top_le_iff.1 ((span_plVec b l).ge.trans ?_))
    refine Ideal.span_le.2 (Set.range_subset_iff.2 fun c => Ideal.mem_span_singleton.2 ?_)
    have := minor_mul 1 b.1 l hb' ((rowsEquiv _ _).symm c)
    rw [one_mul] at this
    exact Dvd.intro_left _ this.symm
  · rw [map_sum]
    simp only [Scheme.Modules.Hom.app_smul, hφ, Loc.colSecOn, Finset.smul_sum, smul_smul, Matrix.submatrix_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    refine Fintype.sum_of_injective (Fin.castLE l.is_le) (Fin.castLE_injective _) _ _ (fun k hk => ?_)
      fun _ => mul_comm _ _
    rw [hb' k _ j.2 (not_lt.1 fun h => hk ⟨⟨k, h⟩, rfl⟩), mul_zero]

private theorem app_pullbackSections_cell (ι : Type) [Fintype ι] (N : ℕ) (a : ι) (l : Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) (e : Γ(F ι N a l, TautCell.cellU w)) (j : Fin N)
    (he : (sub ι N a l).incl.app (TautCell.cellU w) e = TautCell.colU w a j)
    {T : Scheme.{0}} (f : T ⟶ Fl ι N) (V : T.Opens) (hV : V ≤ f ⁻¹ᵁ TautCell.cellU w) :
      ((Scheme.Modules.pullback f).map (incl ι N a l) ≫
        (Scheme.Modules.pullbackComp f (flStr ι N)).hom.app (Taut.stdE N)).app V
          (GlobalTheory.QCoh.pullbackSections f (F ι N a l) hV e) =
        Loc.colSecOn (f ≫ flStr ι N) V
          ((TautCell.cellMat w a).1.map (f.appLE (TautCell.cellU w) V hV).hom) j := by
  have h1 (i : Fin N) : (freeIso ι N).inv.app ⊤ (GlobalTheory.VB.freeFrame (Fl ι N) (Fin N) i) =
      GlobalTheory.QCoh.pullbackSections (flStr ι N) (Taut.stdE N) (U := ⊤) (V := ⊤) le_top
        (GlobalTheory.VB.freeFrame (Sp ℤ) (Fin N) i) := by
    have := ((GlobalTheory.VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (flStr ι N)).iso_hom_app
      (GlobalTheory.VB.isFrame_freeFrame _ (Fin N)) i
    rw [← this]
    exact congr(($((freeIso ι N).hom_inv_id)).app ⊤ _)
  have h2 : (incl ι N a l).app (TautCell.cellU w) e = ∑ i, (TautCell.cellMat w a).1 i j •
      GlobalTheory.QCoh.pullbackSections (flStr ι N) (Taut.stdE N) (U := TautCell.cellU w) (V := ⊤) le_top
        (GlobalTheory.VB.freeFrame (Sp ℤ) (Fin N) i) := by
    refine (congrArg ((freeIso ι N).inv.app (TautCell.cellU w)) he).trans ?_
    rw [TautCell.colU, TautCell.colOn, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Scheme.Modules.Hom.app_smul, app_resM, h1]
    exact congrArg _ (GlobalTheory.QCoh.res_pullbackSections _ _ _ _ _)
  refine (congrArg (((Scheme.Modules.pullbackComp f (flStr ι N)).hom.app (Taut.stdE N)).app V)
    ((GlobalTheory.QCoh.pullback_map_app_pullbackSections f (incl ι N a l) hV e).trans
      (congrArg (GlobalTheory.QCoh.pullbackSections f ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) hV) h2))).trans ?_
  rw [map_sum, map_sum, Loc.colSecOn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul]
  exact congrArg (_ • ·) (LocTaut.pullbackComp_hom_app f (flStr ι N) (Taut.stdE N) (U := ⊤) le_top hV le_top _)

private theorem spMap_cellHom_cell (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N))
    (hU : IsAffineOpen (TautCell.cellU w)) :
    spMap (TautCell.cellHom w) ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = hU.fromSpec := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) hU
    (isAffineOpen_top _) (Scheme.Hom.preimage_image_eq _ ⊤).ge
  have e₀ : ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).hom =
      (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appLE (TautCell.cellU w) ⊤
        (Scheme.Hom.preimage_image_eq _ ⊤).ge :=
    Scheme.Hom.appIso_hom' _ _
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← e₀] at h
  have e : spMap (TautCell.cellHom w) =
      Spec.map ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).inv := by
    exact Spec.map_comp _ _
  rw [e]
  erw [Category.assoc, ← h]
  erw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

private theorem exists_eq_cellMat_mul (ι : Type) [Fintype ι] (N : ℕ) (a : ι) (A : Type) [CommRing A]
    (g : ι → GL (Fin N) A) (w : ι → Equiv.Perm (Fin N)) (y : Sp A)
    (hy : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g y ∈ TautCell.cellU w) :
    ∃ (V : (Sp A).Opens) (hV : V ≤ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ TautCell.cellU w)
      (b : GL (Fin N) Γ(Sp A, V)), y ∈ V ∧ (∀ i j : Fin N, j < i → b.1 i j = 0) ∧
      (g a).1.map ((resG (Sp A) (le_top : V ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
        (TautCell.cellMat w a).1.map
          ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE (TautCell.cellU w) V hV).hom * b.1 := by
  obtain ⟨V, hVa, hyV, hV⟩ := GlobalTheory.QCoh.exists_affine_mem_le
    (U := flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ⁻¹ᵁ TautCell.cellU w) y hy
  have hU : IsAffineOpen (TautCell.cellU w) :=
    (isAffineOpen_top (Sp (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).image_of_isOpenImmersion _
  set ρ := (resG (Sp A) (le_top : V ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom with hρ
  set ψ := ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE (TautCell.cellU w) V hV).hom with hψ
  have h1 : spMap ρ = hVa.fromSpec := by
    have := (isAffineOpen_top (Sp A)).map_fromSpec hVa (homOfLE (le_top : V ≤ ⊤)).op
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    exact (Spec.map_comp _ _).trans this
  have h2 : spMap ψ ≫ hU.fromSpec = hVa.fromSpec ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g :=
    IsAffineOpen.SpecMap_appLE_fromSpec _ hU hVa hV
  rw [← h1, ← spMap_cellHom_cell ι N w hU, cell, spMap_flagPt, spMap_flagPt, spMap_flagPt,
    flagPt_eq_iff_below] at h2
  refine ⟨V, hV, (Matrix.GeneralLinearGroup.map ψ (TautCell.cellMat w a))⁻¹ * Matrix.GeneralLinearGroup.map ρ (g a),
    hyV, fun i j hij => h2 a i j ⟨(a, i.castSucc), rfl, hij, le_rfl⟩, ?_⟩
  exact congrArg Units.val (mul_inv_cancel_left (Matrix.GeneralLinearGroup.map ψ (TautCell.cellMat w a))
    (Matrix.GeneralLinearGroup.map ρ (g a))).symm

end GlobalTheory.FlagZ.Univ

theorem _root_.GlobalTheory.T.universal_flag_frame_specialize : ∀ (ι : Type) [Fintype ι] (N : ℕ) (a : ι) (l : Fin (N + 1)), (∀ w : ι → Equiv.Perm (Fin N), ∃ e : Fin l → Γ(GlobalTheory.FlagZ.Univ.F ι N a l, GlobalTheory.FlagZ.TautCell.cellU w), GlobalTheory.VB.IsFrame e ∧ ∀ j, (GlobalTheory.FlagZ.Univ.sub ι N a l).incl.app (GlobalTheory.FlagZ.TautCell.cellU w) (e j) = GlobalTheory.FlagZ.TautCell.colU w a (Fin.castLE l.is_le j)) → GlobalTheory.VB.IsVB (GlobalTheory.FlagZ.Univ.F ι N a l) l → ∀ (A : Type) [CommRing A] (g : ι → GL (Fin N) A), ∃ s : Fin l → Γ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).obj (GlobalTheory.FlagZ.Univ.F ι N a l), ⊤), GlobalTheory.VB.IsFrame s ∧ ∀ j, ((Scheme.Modules.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).map (GlobalTheory.FlagZ.Univ.incl ι N a l) ≫ (Scheme.Modules.pullbackComp (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g) (flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N)).app ⊤ (s j) = GlobalTheory.FlagZ.Taut.colSec (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j) := by
  intro ι _ N a l hcell hVB A _ g
  haveI := hVB.isQuasicoherent
  refine GlobalTheory.FlagZ.Univ.exists_frame_of_local _ (fun j => GlobalTheory.FlagZ.Taut.colSec
    (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) (g a).1 (Fin.castLE l.is_le j)) fun y => ?_
  obtain ⟨w, x, hx⟩ := GlobalTheory.FlagZ.exists_mem_range_cell _ _ _ (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd
    (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g y)
  have hy : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g y ∈ GlobalTheory.FlagZ.TautCell.cellU w := ⟨x, trivial, hx⟩
  obtain ⟨V, hV, b, hyV, hb, hgb⟩ := GlobalTheory.FlagZ.Univ.exists_eq_cellMat_mul ι N a A g w y hy
  obtain ⟨e, he, hinc⟩ := hcell w
  have he' : GlobalTheory.VB.IsFrame fun j => GlobalTheory.QCoh.pullbackSections (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)
      (GlobalTheory.FlagZ.Univ.F ι N a l) hV (e j) := by
    have := (he.pullback (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g)).res hV
    convert this using 2
    exact (GlobalTheory.QCoh.res_pullbackSections _ _ _ _ _).symm
  obtain ⟨hinj, s, hs, hsφ⟩ := GlobalTheory.FlagZ.Univ.exists_frame_mul
    (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g ≫ flStr ι N) _ V l _
    (Matrix.GeneralLinearGroup.map ((flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g).appLE
      (GlobalTheory.FlagZ.TautCell.cellU w) V hV).hom (GlobalTheory.FlagZ.TautCell.cellMat w a)) b he'
    (fun k => GlobalTheory.FlagZ.Univ.app_pullbackSections_cell ι N a l w (e k) _ (hinc k) _ V hV) hb
  refine ⟨V, s, hyV, hs, fun j => ?_, hinj⟩
  rw [hsφ j, GlobalTheory.FlagZ.Univ.resM_colSec, hgb]
  rfl

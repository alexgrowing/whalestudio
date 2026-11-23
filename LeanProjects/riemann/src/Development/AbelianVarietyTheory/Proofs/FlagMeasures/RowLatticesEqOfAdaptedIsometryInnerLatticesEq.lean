import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowRepresentativesUpToFrameAdaptedIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotentStatement

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.SideEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    frame F (Fin.last D.R.rS) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem xflag_top {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Xflag F D.R.rS = Xsp F := by
  simp only [Xflag, Xsp, FlagG.Xa, FlagG.X]
  congr 1
  have : {i : Fin D.R.rS | i.1 < D.R.rS} = Set.univ := by ext i; simp [i.2]
  rw [this, Set.image_univ]

theorem xflag_mono {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {i j : ℕ} (h : i ≤ j) : Xflag F i ≤ Xflag F j := by
  exact Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => (lt_of_lt_of_le hk h : k.1 < j))

theorem xflag_eq_range {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    Xflag F j = Submodule.span D.host.E (Set.range fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1) := by
  simp only [Xflag, FlagG.Xa]
  congr 1
  ext x; simp

theorem finrank_xflag_eq {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  rw [(LinearEquiv.ofEq _ _ (xflag_eq_range F j)).finrank_eq]
  exact finrank_span_eq_card (F.fl.e_indep.comp (fun i : {i : Fin D.R.rS // i.1 < j} => i.1) Subtype.val_injective)

theorem finrank_xflag {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (G : LFlag (VS D) D.R.rS T') (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag G j) := by
  rw [finrank_xflag_eq, finrank_xflag_eq]

theorem map_xflag_le {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
  simp only [Xflag, FlagG.Xa]
  rw [Submodule.map_span_le]
  rintro _ ⟨i, hi, rfl⟩
  have h1 := hg.2 (Fin.castSucc i)
  rw [frame_castSucc, frame_castSucc] at h1
  have e : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) = (g (F.fl.e i) - G.fl.e i) + G.fl.e i := by
    simp
  rw [e]
  refine add_mem ?_ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hle := xflag_mono G (show (Fin.castSucc i).val ≤ j from le_of_lt hi)
  exact hle h1

theorem map_xflag {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) (j : ℕ) :
    (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j := by
  haveI : FiniteDimensional D.host.E (Xflag G j) :=
    FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  refine Submodule.eq_of_le_of_finrank_eq (map_xflag_le hg j) ?_
  rw [LinearEquiv.finrank_map_eq]
  exact finrank_xflag F G j

theorem map_xsp {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  rw [← xflag_top, ← xflag_top]; exact map_xflag hg _

theorem adapt_mul {T : D.host.E} {F G H : LFlag (VS D) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have e : (g' * g) (frame F a) - frame H a = g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    change g' (g (frame F a)) - frame H a = _
    rw [map_sub]; abel
  rw [e]
  refine add_mem ?_ (hg'.2 a)
  rw [← map_xflag hg' a.val]
  exact Submodule.mem_map_of_mem (hg.2 a)

theorem adapt_inv {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) :
    Adapt g⁻¹ G F := by
  refine ⟨inv_mem hg.1, fun a => ?_⟩
  have hm := map_xflag hg a.val
  have h2 := hg.2 a
  rw [← hm] at h2
  obtain ⟨y, hy, hye⟩ := h2
  have e : g⁻¹ (frame G a) - frame F a = -y := by
    have : g (frame F a - y) = frame G a := by
      rw [map_sub]; simp only [LinearEquiv.coe_coe] at hye; rw [hye]; abel
    rw [← this]
    show g.symm (g (frame F a - y)) - frame F a = -y
    rw [LinearEquiv.symm_apply_apply]; abel
  rw [e]; exact neg_mem hy

theorem z_mem_orth {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : F.fl.z ∈ orth (VS D) (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  simp only [Xsp, FlagG.X] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact F.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem nrat_adapt {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) : Adapt n F F := by
  refine ⟨hn.1, fun a => ?_⟩
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_top]
    exact hn.2.2 _ (z_mem_orth F)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inj (g : GV D) {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap g M = Formalism.HermitianLatticesTheory.gmap g N) : M = N := by
  have := congrArg (Formalism.HermitianLatticesTheory.gmap g⁻¹) h
  rwa [← gmap_mul, ← gmap_mul, inv_mul_cancel, gmap_one, gmap_one] at this

theorem map_toO (g : GV D) (U : Submodule D.host.E (VS D).V) :
    (toO (VS D) U).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      toO (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext x
  simp only [toO, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply]

theorem map_orth {g : GV D} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (U : Submodule D.host.E (VS D).V) :
    (orth (VS D) U).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) =
      orth (VS D) (U.map (g : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext y
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩ x ⟨u, hu, rfl⟩
    rw [hg u w]; exact hw u hu
  · intro h
    refine ⟨g.symm y, fun x hx => ?_, by simp⟩
    have := h (g x) ⟨x, hx, rfl⟩
    rw [← hg x (g.symm y)]
    simpa using this

theorem lsub_map {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {g : GV D} (hg : Adapt g F G) (Λ : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap g Λ) G = Formalism.HermitianLatticesTheory.gmap g (Lsub Λ F) := by
  have hinj : Function.Injective ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) :=
    g.injective
  simp only [Lsub, Lrep, Formalism.HermitianLatticesTheory.gmap]
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj, map_toO, map_toO, map_orth hg.1,
    map_xsp hg]

theorem side : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (VS D) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  intro D X Y v B ψ₀ ψ₁ Λa Λb ha hb A0 A1 hL
  have As : Adapt (ψ₁⁻¹ * ψ₀) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul A0 (adapt_inv A1)
  have hsub : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁⁻¹ * ψ₀) Λa) (lf D (X.Fu v)) = Lsub Λb (lf D (X.Fu v)) := by
    apply gmap_inj ψ₁
    rw [← lsub_map A1, ← lsub_map A1, ← gmap_mul, mul_inv_cancel_left]
    exact hL
  obtain ⟨n, hn, hnΛ⟩ := GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu v) Λa Λb (ψ₁⁻¹ * ψ₀) ((Y.rowsOK v).1 Λa ha)
    ((Y.rowsOK v).1 Λb hb) As hsub
  have Ans : Adapt (n * (ψ₁⁻¹ * ψ₀)) (lf D (X.Fu v)) (lf D (X.Fu v)) := adapt_mul As (nrat_adapt hn)
  have heq : Λa = Λb := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y v v).2 Λb hb Λa ha _ Ans hnΛ
  exact ⟨heq.symm, n, hn, Ans, hnΛ.trans heq.symm⟩

end GlobalTheory.Unfold.SideEq

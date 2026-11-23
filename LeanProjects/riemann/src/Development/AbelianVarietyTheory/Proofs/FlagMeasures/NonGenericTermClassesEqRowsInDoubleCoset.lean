import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowCls

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_apply {U : Submodule E S.V} {x : S.V} (hx : x ∈ orth S U) {y : S.V} (hy : y ∈ U) :
    S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
  exact hx y hy

theorem mem_orth_of {U : Submodule E S.V} {x : S.V} (h : ∀ y ∈ U, S.hT y x = 0) : x ∈ orth S U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  exact h

theorem mem_orth_Xsp {T : E} (F : LFlag S r T) (x : S.V) (hx : ∀ a, S.hT (F.fl.e a) x = 0) :
    x ∈ orth S (Xsp F) := by
  refine mem_orth_of fun y hy => ?_
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact hx a
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem frame_orth_Xsp {T : E} (F : LFlag S r T) (i : Fin (r + 1)) (y : S.V) (hy : y ∈ Xsp F) :
    S.hT (F.fl.fvec i) y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    induction i using Fin.lastCases with
    | last => rw [FlagG.fvec, Fin.snoc_last, ← S.herm.eq, F.fl.z_orth b, map_zero]
    | cast a => rw [FlagG.fvec, Fin.snoc_castSucc]; exact F.fl.e_iso a b
  | zero => simp
  | add y y' _ _ h h' => simp [h, h']
  | smul c y _ h => simp [h]

theorem mapLF_fvec {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T)
    (i : Fin (r + 1)) : (mapLF γ F).fl.fvec i = γ (F.fl.fvec i) := by
  unfold mapLF
  rw [dif_pos hγ]
  induction i using Fin.lastCases with
  | last => simp [FlagG.fvec, mapFlag]
  | cast a => simp [FlagG.fvec, mapFlag]

end Gen

section NR

variable {D : D7}

theorem nrat_fvec_sub {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) (i : Fin (D.R.rS + 1)) : n (F.fl.fvec i) - F.fl.fvec i ∈ Xsp F := by
  induction i using Fin.lastCases with
  | last =>
    rw [FlagG.fvec, Fin.snoc_last]
    exact hn.2.2 _ (mem_orth_Xsp F _ F.fl.z_orth)
  | cast a =>
    rw [FlagG.fvec, Fin.snoc_castSucc]
    have h1 : F.fl.e a ∈ Xflag F (a.1 + 1) :=
      Submodule.subset_span ⟨a, by show a.1 < a.1 + 1; omega, rfl⟩
    exact Submodule.span_mono (Set.image_subset_range _ _) (hn.2.1 a.1 _ h1)

theorem nrat_map_Xsp {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NRat F) (y : (VS D).V) (hy : y ∈ Xsp F) : n y ∈ Xsp F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h := nrat_fvec_sub F hn a.castSucc
    rw [FlagG.fvec, Fin.snoc_castSucc] at h
    have h2 : F.fl.e a ∈ Xsp F := Submodule.subset_span ⟨a, rfl⟩
    simpa using (Xsp F).add_mem h h2
  | zero => simp
  | add y y' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul c y _ h => rw [map_smul]; exact Submodule.smul_mem _ c h

theorem one_mem_NRat {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

end NR

end GlobalTheory.Unfold.RowCls

namespace GlobalTheory.Unfold.RowCls

section Terms

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nonGeneric_terms_same_coset_corank_one (t t' : TauC Y u u') (ht : t ∈ (Y.tO u u').ngSet) (hlam : t.lam = t'.lam)
    (hlam' : t.lam' = t'.lam') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NRat (lf D (X.Fu u)))
    (n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn' : n' ∈ NRat (lf D (X.Fu u'))) (he : t'.lin = n * t.lin * n') :
    (Y.tO u u').s0 t t' = 1 := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : Submodule.IsLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact t'.rep.2.2.2.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hiso' : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  show Formalism.L2.SG.TermOp.s0T t t' = 1
  unfold Formalism.L2.SG.TermOp.s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  refine (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 ?_
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp _ _ _ _ _) fun x hx => ?_
  have hxo : ∀ i, (VS D).hT (Sum.elim (lf D (X.Fu u)).fl.fvec t.frame.fl.fvec i) x = 0 := fun i =>
    Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp t.lam _ t.frame hx
      (PI.PairCorankPos.W.frame_mem_UUE t.lam hlat _ t.frame hLF hLt i)
  have hxF : x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
    mem_orth_Xsp _ x fun a => by simpa [FlagG.fvec] using hxo (Sum.inl a.castSucc)
  have hxt : x ∈ orth (VS D) (Xsp t.frame) :=
    mem_orth_Xsp _ x fun a => by simpa [FlagG.fvec] using hxo (Sum.inr a.castSucc)

  have hXt : ∀ d ∈ Xsp (lf D (X.Fu u')), t.lin d ∈ Xsp t.frame := fun d hd =>
    (Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF t.lin hiso (lf D (X.Fu u')) _).2 (by simpa using hd)
  refine Submodule.mem_map.2 ⟨(x, n x), (Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs _ _ _ _ _ _).2 ⟨hx, ?_, ?_, ?_⟩, rfl⟩
  · refine Formalism.L2.SG.NGCut.CorankRelation.mem_Hp_of_orth t.lam _ t'.frame hLF hL' (n x) ?_
    rintro (a | b)
    · show (VS D).hT ((lf D (X.Fu u)).fl.fvec a) (n x) = 0
      have h1 : (VS D).hT ((lf D (X.Fu u)).fl.fvec a) x = 0 := hxo (Sum.inl a)
      have h2 := frame_orth_Xsp (lf D (X.Fu u)) a _ (hn.2.2 x hxF)
      have h3 : n x = x + (n x - x) := by abel
      rw [h3, map_add, h1, h2, add_zero]
    · show (VS D).hT (t'.frame.fl.fvec b) (n x) = 0
      have hf : t'.frame.fl.fvec b = n (t.lin (n' ((lf D (X.Fu u')).fl.fvec b))) := by
        show (mapLF t'.lin (lf D (X.Fu u'))).fl.fvec b = _
        rw [mapLF_fvec t'.lin hiso' _ b, he]
        rfl
      rw [hf, hn.1]
      have hd := nrat_fvec_sub (lf D (X.Fu u')) hn' b
      have h4 : n' ((lf D (X.Fu u')).fl.fvec b) =
          (lf D (X.Fu u')).fl.fvec b + (n' ((lf D (X.Fu u')).fl.fvec b) - (lf D (X.Fu u')).fl.fvec b) := by abel
      have h5 : (VS D).hT (t.lin ((lf D (X.Fu u')).fl.fvec b)) x = 0 := by
        have := hxo (Sum.inr b)
        simp only [Sum.elim_inr] at this
        rwa [show t.frame.fl.fvec b = t.lin ((lf D (X.Fu u')).fl.fvec b) from mapLF_fvec t.lin hiso _ b] at this
      rw [h4, map_add, map_add, LinearMap.add_apply, h5, orth_apply hxt (hXt _ hd), add_zero]
  · show x - n x ∈ Xsp (lf D (X.Fu u))
    have := (Xsp (lf D (X.Fu u))).neg_mem (hn.2.2 x hxF)
    simpa using this
  · show (t'.lin * t.lin⁻¹) x - n x ∈ Xsp t'.frame
    refine (Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF t'.lin hiso' (lf D (X.Fu u')) _).2 ?_
    set w := t.lin.symm x with hw
    have hwx : t.lin w = x := by simp [hw]
    have key : t'.lin (w - n'.symm w) = (t'.lin * t.lin⁻¹) x - n x := by
      rw [he]
      show n (t.lin (n' (w - n'.symm w))) = n (t.lin (n' (t.lin.symm x))) - n x
      rw [← hw, map_sub, LinearEquiv.apply_symm_apply, map_sub, map_sub, hwx]
    rw [← key, LinearEquiv.symm_apply_apply]

    have hwo : ∀ y ∈ Xsp (lf D (X.Fu u')), (VS D).hT y w = 0 := fun y hy => by
      rw [← hiso y w, hwx]
      exact orth_apply hxt (hXt y hy)
    have hv : n'.symm w ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) := by
      refine mem_orth_of fun y hy => ?_
      rw [← hn'.1 y (n'.symm w), LinearEquiv.apply_symm_apply]
      exact hwo _ (nrat_map_Xsp _ hn' y hy)
    have h6 := hn'.2.2 _ hv
    rw [LinearEquiv.apply_symm_apply] at h6
    exact h6

theorem clsRow_ngSet : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    ClsRow (Y.tO u u').ngSet (clsOf Y u u') := by
  intro D X Y u u' hT t ht t' ht' hn
  obtain ⟨hR, hS, hTr⟩ := Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds D X Y u u' hT
  have hiff : clsOf Y u u' t = clsOf Y u u' t' ↔
      ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ (Y.tO u u').s0 t t' = 1) := by
    constructor
    · intro heq
      have hm : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hR t' ht'⟩
      rw [← heq] at hm
      exact ⟨hm.2.1.symm, hm.2.2⟩
    · rintro ⟨hr, hs⟩
      ext x
      simp only [Formalism.L2.SG.RowsConc.clsOf, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hx, hrx, hsx⟩
        exact ⟨hx, hrx.trans hr, hTr t' ht' t ht x hx hr.symm hrx.symm (hS t ht t' ht' hr hs) hsx⟩
      · rintro ⟨hx, hrx, hsx⟩
        exact ⟨hx, hrx.trans hr.symm, hTr t ht t' ht' x hx hr hrx.symm hs hsx⟩
  rw [hiff]
  refine ⟨fun h => h.1, fun hr => ⟨hr, ?_⟩⟩
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]
    exact ⟨1, one_mem_NRat _, 1, one_mem_NRat _, by simp⟩
  obtain ⟨n, hnn, n', hnn', he⟩ := hmem
  exact nonGeneric_terms_same_coset_corank_one t t' ht hlam hlam' n hnn n' hnn' he

end Terms

end GlobalTheory.Unfold.RowCls

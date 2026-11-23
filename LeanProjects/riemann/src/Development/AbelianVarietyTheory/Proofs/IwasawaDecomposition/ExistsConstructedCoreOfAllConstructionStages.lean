import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParametersForcedContentEqScaleAtResidueCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumnsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLayerConditionsTrueColumnsLaterStagesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsGaugeOfIsCMExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.CoreAsm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {𝒮 : Slots} {w : ColW B f T} {Z : w.Lt}

theorem fval_off (l : Lv4 𝒮 K w Z) (L : SizeData₂ (w.D Z)) (hL : L.sc = K.s) (v : B.places.Pl) (hv : v ∉ l.Wt)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts (w.D Z)) : Fval L j v = 0 := by
  refine (GlobalTheory.T.forcedContent_eq_scale_at_residueChar (w.D Z) L j v).trans ?_
  rw [hL]
  rw [l.what₂.exact] at hv
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have hv' := fun (i : Fin (w.D Z).R.m) h => hv ⟨i, (w.D Z).plEq v, Or.inl rfl, Or.inr (Or.inr h)⟩
  have key : F0K K.s (w.D Z) ((w.D Z).plEq v) ⟨j - 1, by omega⟩ = 0 := by
    by_contra h
    exact hv' _ h
  unfold F0K at key
  simp only [Equiv.symm_apply_apply] at key
  have e : j - 1 + 1 = j := by omega
  rw [e] at key
  exact key

theorem not_mem_of_untw (l : Lv4 𝒮 K w Z) (v : B.places.Pl) (hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0) : v ∉ l.Wt := by
  intro hvW
  have h1 := l.what₂.mu.on v hvW
  have h2 := l.what₂.mu.tw v
  have h3 := l.what₂.mu.mu0
  have hne := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).2.1 v
  apply hne
  rw [← h2, ← h1]
  change w.I.xi ((w.D Z).what₂.muAt v) = 1
  rw [hv]
  exact h3

theorem rowLay_of (l : Lv4 𝒮 K w Z) (Y : DivX (w.D Z)) (hMj : MjAre l.what₂.r.Z Y)
    (hk : ∀ σ, Y.kapR σ = kapSharp (w.D Z)) : V4.RowLay (w.D Z) l.p0 Y where
  rrDef := (Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRDef _).1 l.what₂.r.Z.rr
  rationalRoots_def := l.what₂.r.Z.rr0
  kap_def := l.what₂.r.Y.kap
  lam_def := l.what₂.r.Y.lam
  bu_def := l.what₂.r.Y.bu
  ft_occ := l.what₂.r.Y.occ
  untw := fun v hv j h1 h2 => l.what₂.untw v (not_mem_of_untw l v hv) j h1 h2
  idx := l.what₂.idx Y hMj
  kapR_def := hk _

theorem stepW_core (_h2b : StandardLattice.SiegelMassRatioCM) : ∀ 𝒮 : Slots, AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
    StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)) := by
  intro 𝒮 hA hD hT
  have hp : StepW (pinAnd (Has4 𝒮)) Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have hAll := hp.trans (((hA.and hD).and hT).and GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns)
  refine (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ h => h) hAll).trans (StepW.of_all ?_)
  rintro K B f T w hO hF ⟨⟨⟨pin⟩, Z, ⟨l⟩⟩, ⟨⟨hAm, hDv⟩, hTh⟩, hGy⟩
  obtain ⟨a, a0, ha⟩ := hAm Z l
  obtain ⟨Y, ⟨dv⟩, hMj, hk, hox⟩ := hDv Z l
  obtain ⟨th, ⟨tt⟩⟩ := hTh Z l
  obtain ⟨Gy, ker, hgy, kt, Pl, Bs, hh, he⟩ := hGy Z l.col l.Wt l.nch l.n Y l.what₂.mu dv.Qp
  obtain ⟨G, hG⟩ := GlobalTheory.GaugeEx.exists_isGauge (w.D Z).host.F (w.D Z).host.E (w.D Z).sp.cm
  let O : Obj2 (w.D Z) :=
    { gatT := l.col.Gt, th := th, cmp := l.col.cmp, tw := w.tw Z, Gy := Gy, errX := Formalism.L2.Herm.toErrXS l.col.full.1,
      nch := l.nch, xd := l.xd, lev := l.col.full.1.base.lev0, X := Y, p0 := l.p0, ker := ker, amb := a, amb0 := a0,
      gauge := G }
  obtain ⟨ox⟩ := hox O l.what₂ rfl rfl HEq.rfl
  let c : V4.Core K (w.st Z) f T :=
    { isOver := hO
      xi := w.I.xi
      Wt := l.Wt
      mu := l.what₂.mu
      forced := hF
      fval := fun L hL _ _ v hv j hj => fval_off l L hL v hv j hj
      O := O
      col := GlobalTheory.T.columnLayerConditions_trueColumns_laterStages B f T w Z l.col.toColT
      gatNum := (l.g Z.W Z.V Z.S Z.N).2.1
      gy := hgy
      row := rowLay_of l Y hMj hk
      mtStable := l.what₂.r.Y.stable
      th_io := tt.io
      gauge_def := hG
      real := l.real
      dsig_eq := l.dsig_eq
      del := l.del
      etaF := l.what₂.etaF
      chiT := l.chiT
      nch_tie := l.n.tie
      nch_Q := l.n.Q }
  let bt : Built 𝒮 K w Z c :=
    { pin := pin
      coh := l.coh
      g := l.g
      col := l.col
      what₂ := l.what₂
      rx := l.rx
      xi := rfl
      lev := rfl
      errX := rfl
      n := l.n
      nx := l.nx
      sx := l.sx
      ker0 := ker
      ker_eq := rfl
      ker := kt
      div := dv
      th := tt
      obj := ⟨ha, hMj, hk⟩
      ox := ox }
  exact ⟨Z, c, bt, Pl, Bs, hh, he⟩

end GlobalTheory.Mem.Top.Bl.CoreAsm

end

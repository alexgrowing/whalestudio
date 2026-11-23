import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevOfRed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMemLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.Rows

open GlobalTheory.FinPl

section Gen

variable {D : D7}

theorem idAt_le {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p) {z : AE D} (hz : z ∈ idAt D P) : z ∈ idAt D Q := by
  simp only [idAt, Submodule.mem_inf, idOff, Submodule.mem_iInf] at hz ⊢
  exact ⟨hz.1, fun w => hz.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem moves_mono {V : HSp D} {g : GA D V} {L : GlobalTheory.FinPl.Lat V} {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p)
    (H : GlobalTheory.FinPl.Moves V g L L Q) : GlobalTheory.FinPl.Moves V g L L P := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D Q := fun i => idAt_le h (hy i)
  rw [MovesSplit.mem_latV_iff_all V L P hy, MovesSplit.mem_latV_iff_all V L P (KOpen.supp_mulVec V P g hy),
    ← MovesSplit.mem_latV_iff_all V L Q hy', ← MovesSplit.mem_latV_iff_all V L Q (KOpen.supp_mulVec V Q g hy')]
  exact H y hy'

theorem st_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : GlobalTheory.FinPl.Lat V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ)
    (g : GA D V) : finE V g ∈ St β ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves V g Λ Λ (· = v) := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
  exact forall_congr' fun v => (GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v _).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem moves_of_stab (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (t x : GA D V)
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (bas : GL Y k)
    (σ : Fin V.rank ≃ Y) (hM : MovedTo (ofSplit q) V t β ((F.β * bas.val).submatrix id σ))
    (m : GL Y k) (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hs : m ∈ stabLat bas) :
    GlobalTheory.FinPl.Moves V (t⁻¹ * x * t) Λ Λ (· = q.v) := by
  have h1 : (mt V t⁻¹).map q.pr * (mt V t).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', inv_mul_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (mt V t).map q.pr * (mt V t⁻¹).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', mul_inv_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  let F' : GlobalTheory.LocMod.Frame k V.rank Y := ⟨(mt V t⁻¹).map q.pr * F.β, F.γ * (mt V t).map q.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((mt V t).map q.pr), h2, Matrix.one_mul, F.γβ]⟩
  have hM' : MovedTo (ofSplit q) V 1 β ((F'.β * bas.val).submatrix id σ) := by
    intro b hb
    have h3 : (mt V t).map q.pr * b.map q.pr = (F.β * bas.val).submatrix id σ := by
      rw [← Matrix.map_mul]; exact hM b hb
    have h4 : (F'.β * bas.val).submatrix id σ = (mt V t⁻¹).map q.pr * (F.β * bas.val).submatrix id σ := by
      show ((mt V t⁻¹).map q.pr * F.β * bas.val).submatrix id σ = _
      rw [Matrix.mul_assoc]
      rfl
    rw [h4, ← h3, ← Matrix.mul_assoc, h1, Matrix.one_mul, LevRed.mt_one', Matrix.one_mul]
    rfl
  have h0 : GlobalTheory.FinPl.Moves V 1 Λ Λ (· = q.v) := fun y _ => by rw [LevRed.mt_one', Matrix.one_mulVec]
  have hl := LevMoves.isLat_moved q hq V Λ Λ β hβ 1 h0 F' bas σ hM'
  obtain ⟨gl, g1, g2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V _ F'.β F'.γ F'.βγ F'.γβ
  refine (GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes D k q V _ ⟨F'.β, F'.γ, F'.βγ, F'.γβ, gl, g1, g2⟩ Λ _ hΛ hl _).2 ?_
  have h5 : (mt V (t⁻¹ * x * t)).map q.pr = F'.β * m.val * F'.γ := by
    rw [LevRed.mt_mul', LevRed.mt_mul', Matrix.map_mul, Matrix.map_mul, hm]
    simp only [F', Matrix.mul_assoc]
  have h6 := (eq_coordHom_iff V q.pr F'.β F'.γ F'.βγ F'.γβ _ _).1 h5
  exact h6 ▸ LevMoves.smul_latOf hs

end Gen

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem red_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (β : GL (Fin V.rank) (Lev.EAf D)) (t x : GA D V) {s : ℕ} (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k)
    (F : GlobalTheory.LocMod.Frame k V.rank (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)))
    (e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) 0 ≃ Fin V.rank) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (hM : MovedTo (ofSplit q) V t β ((F.β * ((S.T (Fin D.R.t)).bas 0 (s + 1) (Nat.zero_add _)).val).submatrix id
      fun a => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _) (e.symm a)))
    (hr : D.R.r ≤ V.rank) (m : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)) k)
    (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hst : finE V (t⁻¹ * x * t) ∈ St β) :
    (∃ z : S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin (s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ c : 𝓞 D.host.E,
        Ideal.Quotient.mk PP.asIdeal c = (upperLeftBlock hr (redFn β PP (finE V (t⁻¹ * x * t)))).val a' b' →
        valuation k ((z : GL (Fin D.R.k ⊕ Fin (s + 1)) k).val a b - (ofSplit q).pr (c : D.host.E)) < 1) ↔
      m ∈ ((S.T (Fin D.R.t)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨w, hw⟩ := hst
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D _ q PP hq
  have h1 := RedLev.mul_moved (ofSplit q) hπ _ _ _ _ w hw hM
  have h3 := RedLev.conj_eq F ((S.T (Fin D.R.t)).bas 0 _ (Nat.zero_add _)) m
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) _
    ((congrArg (· * _) hm).symm.trans h1)
  have hk : D.R.k + (s + 1) = D.R.r := by
    unfold Ranks.r
    omega
  have hlt : ∀ i : Fin V.rank, i.val < D.R.r := fun i => by
    obtain ⟨i, rfl⟩ := e.surjective i
    rw [he, ← hk]
    rcases i with (i | i) | i
    · exact lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left i.2 _
    · exact i.1.elim0
  have htri : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) w ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) :=
    Formalism.L2.DIV.mem_blockTri.2 fun i j h => by simp [Formalism.L2.DIV.blk2, hlt] at h
  have hpos : ∀ i, (e (.inl i)).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i := fun i => by
    rw [he]
    rcases i with i | i <;> rfl
  let T := typeFrame S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _))
  let g := (reGL (ixZero _ (Fin D.R.t))).symm (T.conj.symm m)
  have hg : ∀ i j, g.val i j = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w.val (e (.inl i)) (e (.inl j))) :=
    fun i j => by
      have := congrFun (congrFun h3 (e (.inl i))) (e (.inl j))
      simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, Matrix.map_apply] at this
      exact this
  have h6 : ∀ i j (c : 𝓞 D.host.E),
      Ideal.Quotient.mk PP.asIdeal c = Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))) →
      valuation k (g.val i j - (ofSplit q).pr (c : D.host.E)) < 1 := fun i j c hc => by
    have h5 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E c) =
        (ofSplit q).pr (c : D.host.E) := hπ (incA D (c : D.host.E))
    rw [hg, ← h5, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, hc, sub_self]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨g', hg', e'⟩ := S.P.exists_of_congr z.2 (M := g.val) fun i j => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))))
      have h4 := hz i j ⟨_, hlt (e (.inl i))⟩ ⟨_, hlt (e (.inl j))⟩ (hpos i) (hpos j) c
        (by rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri]; exact hc)
      have := Valuation.map_sub_lt _ (h6 i j c hc) h4
      rwa [sub_sub_sub_cancel_right] at this
    obtain rfl : g' = g := Units.ext e'
    exact hg'
  · intro hJ
    refine ⟨⟨g, hJ⟩, fun i j a' b' ha hb c hc => h6 i j c ?_⟩
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri, Matrix.submatrix_apply] at hc
    have ea : Fin.castLE hr a' = e (.inl i) := Fin.ext (ha.trans (hpos i).symm)
    have eb : Fin.castLE hr b' = e (.inl j) := Fin.ext (hb.trans (hpos j).symm)
    rw [ea, eb] at hc
    exact hc

end Loc

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem mem_rJ_iff (W : RealPack ex) (y : GA D (Yc D 0)) (hy : y ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from y) ∈ rJ W ↔ finE (Yc D 0) y ∈ St ((pk W).βY 0) ∧
      (fun PP : (pk W).Pg => upperLeftBlock (r_le_Y 0) (redFn ((pk W).βY 0) PP.1 (finE (Yc D 0) y))) ∈ (lvP W).H := by
  have hn : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have key := (GlobalTheory.LevYZero.lev_datY_zero (Yc D 0) ((pk W).βY 0) _ D.R.r D.R.t (r_le_Y 0) hn (pk W).Pg (lvP W) (pk W).chi
    (fun _ => 1) rfl (finE (Yc D 0) y) (GlobalTheory.LevSplit.finE_mem_UA _ y)).1
  exact Iff.trans ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩ key

set_option maxHeartbeats 1000000 in

theorem main (W : RealPack ex) (hW : PkHyp W) (u : D.what₂.Word) (a : GeoAll W u) (ha : a.Is)
    (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t)))
    (x : GA D (Yc D 0)) (hx : x ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from (a.g.b 0)⁻¹ * x * a.g.b 0) ∈ rJ W ↔ InYLev a x := by
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hb : a.g.b 0 ∈ GfC (Yc D 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hsd := hW.bot.hyp.2.2.2.1.lev.βY 0 hm
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hsd
  obtain ⟨c, hβ, -⟩ := hsd
  have hoff := GlobalTheory.StMoves.moves_conj_iff x (hV.moves 0 hm (fun p => p ∉ a.v.gP) fun _ h => h)
  choose e he hM using fun i => hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hex : ∀ i, ∃ m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m := fun i =>
    ⟨_, (eq_coordHom_iff _ (a.G i).q.pr _ _ ((a.G i).FY 0 _ (Nat.zero_add _)).βγ ((a.G i).FY 0 _ (Nat.zero_add _)).γβ x _).2 rfl⟩
  have hloc := fun i m (hmat : (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m) hst =>
    red_iff (a.G i).q (hG.idem i).1 (Yc D 0) ((pk W).βY 0) (a.g.b 0) x (a.G i).hs (a.G i).S _ (e i) (he i) (hM i) (r_le_Y 0) m hmat hst
  rw [mem_rJ_iff W _ (mul_mem (mul_mem (inv_mem hb) hx) hb), (hG.lev _).1]
  constructor
  · rintro ⟨hst, hred⟩
    refine ⟨hoff.1 (moves_mono (fun _ _ => trivial) ((movesLocal D _ _ hΛ _).2 ((st_iff _ _ _ hβ hΛ _).1 hst))), ?_⟩
    exact fun i m hmat => (hloc i m hmat hst).1 (hred i)
  · rintro ⟨h1, h2⟩
    have hst : finE (Yc D 0) ((a.g.b 0)⁻¹ * x * a.g.b 0) ∈ St ((pk W).βY 0) := by
      refine (st_iff _ _ _ hβ hΛ _).2 fun v => ?_
      by_cases hv : v ∈ a.v.gP
      · obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
        obtain ⟨m, hmat⟩ := hex i
        have hR : ((a.G i).S.T (Fin D.R.t)).Regular := GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
        exact moves_of_stab (a.G i).q (hG.idem i).1 (Yc D 0) _ _ hβ hΛ (a.g.b 0) x _ _
          ((e i).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) (hM i) m hmat
          ((hR.2.2 0 _ (Nat.zero_add _)).2.2 (h2 i m hmat))
      · exact moves_mono (fun p hp => by rw [hp]; exact hv) (hoff.2 h1)
    refine ⟨hst, fun i => ?_⟩
    obtain ⟨m, hmat⟩ := hex i
    exact (hloc i m hmat hst).2 (h2 i m hmat)

end Real

end GlobalTheory.FamTrace.Rows

theorem GlobalTheory.FamTrace.conj_mem_rows_iff : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ x ∈ GfC ((I.rec7 l Z).sp.Y 0), ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * x * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ rJ W ↔ GlobalTheory.FamTrace.InYLev a x) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ x hx
  exact GlobalTheory.FamTrace.Rows.main W hA.pk u a ha row col x hx

end

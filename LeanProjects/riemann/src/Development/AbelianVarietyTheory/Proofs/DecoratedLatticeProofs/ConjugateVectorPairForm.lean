import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomHypothesisMatchingCentral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugateStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7}

theorem inner_sp {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E) (m : Dc.Mem)
    (c : Fin (Dc.a m) → ℂ) :
    ⟪sEE e, Sp.Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m).op (ramCrd (bR m) c)⟫_ℂ := by
  subst hSp
  obtain rfl := eq_of_heq h
  exact inner_spOf s Dc hK Gd wdD pw bR m _ c

theorem inner_join {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Z : Type}
    {sd : Z → DefSide Bs} (Dcf : ∀ z, DefCols (sd z)) (Spf : ∀ z, SPer (Dcf z)) (z0 z1 : Z) (hz : z0 = z1)
    (Dc : DefCols (sd z1)) (hdc : Dcf z1 = Dc) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hsp : HEq (Spf z1) (spOf s Dc hK Gd wdD pw bR))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] (Spf z0).HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E)
    (m : (Dcf z0).Mem) (m' : Dc.Mem) (hm : HEq m m') (c : Fin ((Dcf z0).a m) → ℂ) (c' : Fin (Dc.a m') → ℂ)
    (hc : HEq c c') :
    ⟪sEE e, (Spf z0).Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m').op (ramCrd (bR m') c')⟫_ℂ := by
  subst hz
  subst hdc
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hc
  exact inner_sp s (Dcf z0) hK Gd wdD pw bR (Spf z0) (eq_of_heq hsp) sEE sEEc h e m c

theorem iota_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) (x : I.GA) :
    ι.symm x = ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x := by
  subst h
  obtain rfl := eq_of_heq hι
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem op_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) (y : (D.mem u).A.Mu0)
    (T : Cu X u hK) (hT : Formalism.L2.SG.ColDict.colDictL X p.Tr hK T = (y : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    ((p.op y : HHX X) : L2X X) = PuFun X u hK p.Dt T := by
  have hd : (Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  show ((Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin
    ((Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y) : HHX X) : L2X X) = _
  rw [hd]
  rfl

theorem op_col (W : RealPack ex) (u w : D.what₂.Word) (hwu : w = u) (hc : W.P.I.wU w = W.P.I.wU u)
    (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (hT : IsCol W u T (colC W u x)) :
    (((pwOf W.S W.Q.hin w).op (ramCrd (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) x) : HHX W.S.X) : L2X W.S.X) =
      PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T := by
  subst hwu
  have hi : ∀ i : Fin (W.P.Dc.a (W.P.I.wU w)), Fin.cast (congrArg W.P.Dc.a hc).symm i = i := fun i => Fin.ext rfl
  have hfun : (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) =
      (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) := by
    funext i
    exact congrArg (fun k => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single k (1 : D.what₂.LL))))) (hi i)
  rw [hfun]
  have hr : Fintype.linearCombination ℂ (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) x =
      D.eMu w (colC W w x) := by
    refine (Fintype.linearCombination_apply ℂ _ x).trans ?_
    simp [colC, map_sum, map_smul]
  refine op_eq (pwOf W.S W.Q.hin w) _ T ?_
  show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr w) W.S.Y.hK T = _
  refine hT.trans ?_
  show _ = ((Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ _ x) : (D.mem w).A.Mu0) : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)
  exact congrArg (fun z : (D.mem w).A.Mram => (z : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)) hr.symm

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

theorem exists_eval {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St}
    {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c)
    (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∀ T : E, ∃ F : L2X St,
      ((F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t (PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ v₀))) ∧
      star F ∈ HHX St ∧ ((sEEofTT M μ 𝓕 E St Gd ι t c T : HHX St) : L2X St) = star F := by
  refine ⟨hE.choose, hE.choose_spec.1, fun T => ⟨(hE.choose_spec.2.choose T : EEC St Gd), ?_, ?_, ?_⟩⟩
  · refine (hE.choose_spec.2.choose_spec T).1.trans (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ι.symm x = (iotaX St h).symm x := iota_symm_eq h ι hι x
    show (T : MMap M) hE.choose (ι.symm x * t) =
      PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ hE.choose) ((iotaX St h).symm x * t)
    rw [h1]
    exact (congrFun (PiTensorProduct.lift.tprod (φ := (T : MMap M)) hE.choose) _).symm
  · exact ((mem_EEC St Gd _).1 (hE.choose_spec.2.choose T).2).1
  · unfold sEEofTT
    simp only [dif_pos hE]
    rfl

theorem inner_smul_star {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (f g : GA D (D.sp.Y 0) → ℂ) (l a : ℂ) (hfg : f = l • g) (F φ P : L2X St)
    (hF : (F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t f) (hφ : (φ : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t g)
    (y z : HHX St) (hy : (y : L2X St) = star F) (hz : (z : L2X St) = P) :
    ⟪a • y, z⟫_ℂ = starRingEnd ℂ a * l * ⟪star φ, P⟫_ℂ := by
  have h1 : F = l • φ := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hF, hφ, MeasureTheory.Lp.coeFn_smul l φ] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, hfg]
    rfl
  have h2 : star (l • φ) = starRingEnd ℂ l • star φ := (Formalism.L2.SG.RowDict.conjL (muX St)).map_smulₛₗ l φ
  rw [inner_smul_left, Submodule.coe_inner, hy, hz, h1, h2, inner_smul_left, starRingEnd_self_apply, mul_assoc]

theorem pairForm : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → PairForm W v := by
  intro hDS hCusp D L hT Gi Gl Kc Yd cX ex W hB v hv
  have hM := (GlobalTheory.MiTop.botHyp_match W hB).2.2.2.2.2
  obtain ⟨v₀, hv₀, hF⟩ := exists_eval (W.Q.seeEval hB.see.2) W.Q.instEq W.Q.ιS_eq
  have key : ∃ l : ℂ, l ≠ 0 ∧ ∀ e : W.Q.Rl.HE.H,
      W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
        rowOf W e (PiTensorProduct.tprod ℂ v₀) = l • rowOf W e (PiTensorProduct.tprod ℂ v) := by
    by_cases hl : ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v
    · obtain ⟨l, hl0, hl⟩ := hl
      exact ⟨l, hl0, fun e _ => (congrArg (rowOf W e) hl).trans ((rowOf W e).map_smul l _)⟩
    · refine ⟨1, one_ne_zero, fun e he => ?_⟩
      by_cases h0 : rowOf W e = 0
      · rw [h0]
        exact (smul_zero (1 : ℂ)).symm
      · obtain ⟨F, h1, h2, -⟩ := hF ⟨W.Q.Rl.HE.e e, he⟩
        exact absurd (GlobalTheory.T.unit_vector_rows_conjugate hDS hCusp W hB v₀ v hv hv₀ (rowOf W e) (hM e he) h0 F h1 h2) hl
  obtain ⟨l, hl0, hl⟩ := key
  refine ⟨starRingEnd ℂ (W.Q.uS * (W.Q.κS : ℂ)) * l, mul_ne_zero ?_ hl0, ?_⟩
  · have hu : W.Q.uS ≠ 0 := by
      intro h
      have := W.Q.uS_norm
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact (map_ne_zero _).2 (mul_ne_zero hu (Complex.ofReal_ne_zero.2 W.Q.seeK.1.ne'))
  intro e he u m hm x x' hx T b hTc hP
  obtain ⟨φ, hφ, rfl⟩ := hP
  refine (inner_join (twQ W.P) W.Dcf W.Spf (cxW W).zs W.P.Zs W.Q.zs W.P.Dc W.Q.dc W.S.Y.hK W.S.G W.Q.wdD
    (fun y => pwOf W.S W.Q.hin (W.Q.wdD y)) W.Q.bR (W.Q.sp.trans W.Q.spPin) W.Q.sEE W.Q.sEEc W.Q.sEEj e m (W.P.I.wU u) hm
    x' x hx.symm).trans (congrArg (cj (twQ W.P)) ?_)
  obtain ⟨F, h1, -, h3⟩ := hF ⟨W.Q.Rl.HE.e (Tw.out e), he⟩
  have hz := (congrArg (fun b => (((pwOf W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd b x) : HHX W.S.X) : L2X W.S.X))
    (funext (hB.pins.bR_read (W.P.I.wU u)))).trans
    (op_col W u (W.Q.wdD (W.P.I.wU u)) (W.Q.wdD_wU u) (W.Q.wU_wdD (W.P.I.wU u)) x T hTc)
  refine Eq.trans ?_ (inner_smul_star W.Q.instEq _ _ _ l (W.Q.uS * (W.Q.κS : ℂ)) (hl (Tw.out e) he) F φ _ h1 hφ _ _ h3 hz)
  exact congrArg (fun y => ⟪Tw.out y, (pwOf W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd (W.Q.bR (W.P.I.wU u)) x)⟫_ℂ)
    (W.Q.seeDef e he)

end GlobalTheory.MiTop.PairingL2

end

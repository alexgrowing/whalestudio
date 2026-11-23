import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseLevelDatumLevelEq
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLocalDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol

open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain in

theorem conj_embX_toBlocks₂₂ {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((typeFrame ϖ ord).bas⁻¹ * embX c g * (typeFrame ϖ ord).bas).val.toBlocks₂₂ = 1 := by
  have e1 : (typeFrame ϖ ord).bas.val = fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val := rfl
  have e2 : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val := by
    change (embA n _)⁻¹.val = _
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, show (embX c g).val = fromBlocks g.val 0 0 1 from rfl,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Units.inv_mul]

end GlobalTheory.FamTraceChiCol

noncomputable section
namespace GlobalTheory.FamTraceChiCol

set_option maxHeartbeats 4000000 in

theorem frame_close : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (GlobalTheory.FamTraceChi.reductionYZero W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → ∀ g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → (∀ p q : Fin (I.rec7 l Z).R.k, valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inl p) (Sum.inl q) - g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q))) < 1) ∧ ∀ p q : Fin ((a.G i).s + 1), q.val = p.val + 1 → valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inr p) (Sum.inr q)) < 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i x hx g hg
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hrJ := (GlobalTheory.T.true_geometry_local_data W hW u a ha hat row col hc κ hκ y hy).1 hyU
  have hb : a.g.b 0 ∈ GfC (Yc (I.rec7 l Z) 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hxe : embA a.d.B.d a.d.B.o κ ∈ GfC ((I.rec7 l Z).sp.Y 0) := GlobalTheory.Corev.EmbAGfC.embA_mem_GfC_fin _ _ _ _ _ _ _ _ κ hκ
  have hSt := ((GlobalTheory.FamTrace.Rows.mem_rJ_iff W _ (mul_mem (mul_mem (inv_mem hb) hxe) hb)).1 hrJ).1
  obtain ⟨e, he, hM⟩ := hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hid := (hG.idem i).1
  have hn : (Yc (I.rec7 l Z) 0).rank = (I.rec7 l Z).R.r := by
    rw [(I.rec7 l Z).sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have hr : (I.rec7 l Z).R.r ≤ (Yc (I.rec7 l Z) 0).rank := hn.ge
  have hmi : 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega
  have hbes : (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (pk W) u a.g).B 0 _ hmi →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hmi _ _
    exact key _ (ha.bot.1 hmi) _ _ HEq.rfl HEq.rfl
  have hm := GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ hbes κ g hg
  let σ := e.symm.trans (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _))
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo (a.G i).q (a.pl i).1 hid _ _ _ _ _
    (((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
      GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
      ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.submatrix σ σ) hM ?_ hSt
  swap
  · have hs : ∀ (A : Matrix (Fin (Yc (I.rec7 l Z) 0).rank) (Fin (Yc (I.rec7 l Z) 0).rank) (a.G i).k)
        (M : Matrix (Fin (Yc (I.rec7 l Z) 0).rank) (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1)) (a.G i).k),
        A * M.submatrix id σ = (A * M).submatrix id σ := fun A M => by
      ext r c'; simp [Matrix.mul_apply]
    have e1 : ((Formalism.L2.Theta.mt (Yc (I.rec7 l Z) 0) ((embA a.d.B.d a.d.B.o) κ)).map (a.G i).q.pr) *
        ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β =
        ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β * (GlobalTheory.RootEx.embX ((a.G i).s + 1) g).val := by
      have hm' : (Formalism.L2.Theta.mt (Yc (I.rec7 l Z) 0) ((embA a.d.B.d a.d.B.o) κ)).map (a.G i).q.pr =
          ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β * (GlobalTheory.RootEx.embX ((a.G i).s + 1) g).val *
            ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ := hm
      rw [hm', Matrix.mul_assoc, Matrix.mul_assoc, Frame.γβ, Matrix.mul_one]
    refine Eq.trans (hs _ _) ?_
    refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ id σ σ).symm
    rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc, ← Units.val_mul]
    congr 1
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel_left]
  have hidx : ∀ (p : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a' : Fin (I.rec7 l Z).R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → e.symm (Fin.castLE hr a') = .inl p := fun p a' ha => by
    rw [Equiv.symm_apply_eq]
    refine Fin.ext ?_
    rw [he]
    rcases p with p | p <;> exact ha
  have main : ∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r),
      p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q →
      valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val p q -
        (((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val
            (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _) (.inl p))
            (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _) (.inl q)))) < 1 := by
    intro p q p' q' hp hq
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((GlobalTheory.FamTraceChi.reductionYZero W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ *
      embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q')
    have h1 := hx p q p' q' hp hq z hz
    have h2 := key (Fin.castLE hr p') (Fin.castLE hr q') z (by
      rw [hz]; exact congrFun (congrFun (GlobalTheory.SeeConjReord.rankBlock_val_eq_submatrix_of_le_rank hr hn.le _) p') q')
    simp only [Matrix.submatrix_apply, σ, Equiv.trans_apply, hidx p p' hp, hidx q q' hq] at h2
    have e : ∀ s t w : (a.G i).k, s - t = (s - w) + -(t - w) := fun s t w => by ring
    rw [e _ _ ((ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E))]
    exact Valuation.map_add_lt _ h1 (by rw [Valuation.map_neg]; exact h2)
  refine ⟨fun p q => ?_, fun p q hpq => ?_⟩
  · have hpr : p.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; unfold Ranks.r; omega
    have hqr : q.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; unfold Ranks.r; omega
    have h := main (.inl p) (.inl q) ⟨p.val, hpr⟩ ⟨q.val, hqr⟩ rfl rfl
    have h11 := GlobalTheory.LevX.conj_embX_val (a.G i).S.ϖ
      (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)) g
    have h11' := congrFun (congrFun h11 (.inl (.inl p))) (.inl (.inl q))
    rw [GlobalTheory.StepData.stdOrd_eps, GlobalTheory.StepData.stdOrd_eps] at h
    exact h11' ▸ h
  · have hpr : (I.rec7 l Z).R.k + p.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; have := p.2; unfold Ranks.r; omega
    have hqr : (I.rec7 l Z).R.k + q.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; have := q.2; unfold Ranks.r; omega
    have h := main (.inr p) (.inr q) ⟨_, hpr⟩ ⟨_, hqr⟩ rfl rfl
    have h22 := conj_embX_toBlocks₂₂ (a.G i).S.ϖ
      (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)) g
    have h22' := congrFun (congrFun h22 p) q
    have hne : p ≠ q := fun h => by rw [h] at hpq; omega
    rw [Matrix.one_apply_ne hne] at h22'
    have hs1 : ∀ r : Fin ((a.G i).s + 1), stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)
        (.inl (.inr r)) = .inr r := fun r => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block _ _ 0 _ _ r
    rw [hs1, hs1] at h
    change valuation (a.G i).k (_ - ((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.toBlocks₂₂ p q) < 1 at h
    have e0 : ((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.toBlocks₂₂ p q = 0 := h22'
    rw [e0, sub_zero] at h
    exact h

end GlobalTheory.FamTraceChiCol
end

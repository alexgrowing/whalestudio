import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGCut in

theorem stepNormOneG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepNormOneG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, hGv, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' := hP.1.1
  have hX' := hP.2.2.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := PtPf.frame_mem _ hz' hX'
  rw [← hpt]
  show 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) ∧
    1 ≤ NDPt D.host.rdE (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm))
  have hlead : ∀ q, q ≤ D.R.rS + 1 → ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)),
      (o : D.host.E) = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) q := fun q hq => by
    obtain ⟨o, ho, e⟩ := lead_mem hun (lf D (X.Fu u)) F' hz hX hz' hX' q hq
    exact ⟨o, ho, e.trans (lead_cell _ _ hcell q).symm⟩
  constructor
  · have hGeq := gpt_eq (T := Tu D u) (T' := Tu D u) (lf D (X.Fu u)) F' _ hcell
    obtain ⟨o1, ho1, e1⟩ := hlead (D.R.rS + 1) le_rfl
    obtain ⟨o0, ho0, e0⟩ := hlead D.R.rS (Nat.le_succ _)
    obtain ⟨o1', ho1', e1'⟩ := star_mem_pow _ o1 ho1
    obtain ⟨o0', ho0', e0'⟩ := star_mem_pow _ o0 ho0
    have ex1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) + (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega]; ring
    have ex0 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) + D.R.rS * (2 * D.R.rS + 1 - D.R.rS) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]; ring
    have hm1 : o1 * o1' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex1, pow_add]; exact Ideal.mul_mem_mul ho1 ho1'
    have hm0 : o0 * o0' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex0, pow_add]; exact Ideal.mul_mem_mul ho0 ho0'
    refine one_le_NGPt _ _ (o1 * o1' - (((Tu D u : ℕ) * (Tu D u : ℕ) : ℕ) : 𝓞 D.host.E) * (o0 * o0'))
      (Ideal.sub_mem _ hm1 (Ideal.mul_mem_left _ _ hm0)) ?_ (by rw [hGeq]; exact hGv)
    have e1a : algebraMap (𝓞 D.host.E) D.host.E o1 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) (D.R.rS + 1) := e1
    have e0a : algebraMap (𝓞 D.host.E) D.host.E o0 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) D.R.rS := e0
    have e1b : algebraMap (𝓞 D.host.E) D.host.E o1' = star (algebraMap (𝓞 D.host.E) D.host.E o1) := e1'
    have e0b : algebraMap (𝓞 D.host.E) D.host.E o0' = star (algebraMap (𝓞 D.host.E) D.host.E o0) := e0'
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    unfold GPt
    rw [dlast_eq, dr_eq, map_sub, map_mul, map_mul, map_mul, map_natCast, e1b, e0b, e1a, e0a]
  · refine one_le_NDPt _ fun a => ?_
    have hj : endIdx (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) a ≤ D.R.rS + 1 :=
      (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := hlead _ hj
    have hE := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    exact ⟨o, ho, by rw [e, endMin_eq], (hE a).2⟩

open Formalism.L2.SG.TermOp.Vanish in

theorem stepNormOneG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    Formalism.L2.SG.Pf.MainEqSteps.StepNormOneG := by
  refine stepNormOneG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen

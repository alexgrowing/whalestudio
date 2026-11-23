import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpecStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlaceStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeightsranchOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RhoVrBrAtEqBrStd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel

noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem coP_PtT_eq_blk : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  intro B X I hI l Z l0 u a w φ hφ c
  have hV : φ ((I.perIn u a).tilC c) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) := (hφ _).1
  have hT : ((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) :=
    GlobalTheory.LvT.Built.RealM.trFr_mem _ _ _ _ _ hV
  obtain ⟨F, hF⟩ := (GlobalTheory.TilClass.mem_ValC_iff _ _ _ _).1 hT
  have hW := fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ
  have hS := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
  show actP (I.perIn u a).sgT (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1))
        (fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          ((I.perIn u a).br B.fields.emb B.embLL (B.hcW u)
            (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
              (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c))))))) =
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
      (actP (lamT (B.hcW u) B.R.m) (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
          (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)))))

  rw [← hF, GlobalTheory.TilClass.polOf_fnOf_one, GlobalTheory.TilClass.polOf_fnOf_one]
  have hlam : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = lamT (B.hcW u) B.R.m := funext fun τ => (hW τ).1
  have hsg : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = (I.perIn u a).sgT := funext fun τ => (hW τ).2.1
  refine Eq.trans ?_ (GlobalTheory.Proof.FockBlockMonotone.blk_brOne_eq (ι := B.fields.Tau) (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm _ _ _).symm
  rw [hlam, hsg]
  have key := GlobalTheory.BranchBlock.rhoVr_brAt_eq_brStd (embAt B.embLL B.fields.emb) (N_m_succ B.R) (lamT (B.hcW u) B.R.m)
    (I.perIn u a).sgT (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) (I.perIn u a).tz _ _ hS.2.1 hS.2.2.1 F
  exact congrArg Subtype.val key

end GlobalTheory.PerQ.Co

end

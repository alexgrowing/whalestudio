import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.TopInt

open GlobalTheory.PhiRootVal (RootOrZero phiGS_root phiG_root phiQ_root)
open GlobalTheory.CplTwoInt (intOff_prod ftY_intOff smul_symm_mem repY_mem)

theorem phiTopG_root {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (sharp : Bool) (i j n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTopG (R := R) Ch mu sharp i j n P x) := by
  unfold PhiTopG
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem xiTop_intOff (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (u) (μ)
    (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (Yb : Set (Sp t.X.E (D.R.N i)))
    (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)) (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1)))
    (hY : Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  have hok := t.idx_ok μ
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem topInt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  intro D L hT Gi Gl K Y cX ex t hTop u μ c c' _ x
  obtain ⟨-, -, pt, ix, yb, pT, -, hyb, -, -, hpin, -, -⟩ := hTop u μ
  rw [hpin.2 c c' x]
  exact xiTop_intOff D L hT Gi Gl K Y cX ex t u μ _ _ _ _ _ (hyb c)

end GlobalTheory.TopInt

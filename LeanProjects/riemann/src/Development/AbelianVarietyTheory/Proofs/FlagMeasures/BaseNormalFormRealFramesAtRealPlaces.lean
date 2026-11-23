import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdapted
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.BaseFrame

theorem normal0_one (k r j : ℕ) (hj : j ≤ r) (h0 : j = 0) (z : Fin (2 * r + k + 1) → ℂ) :
    GlobalTheory.Amp.IsNormal0 k r hj (fun _ => 0) 1 z z 1 := by
  subst h0
  refine ⟨?_, by simp, by simp, monotone_const, fun a b _ => by simp, fun a ha => absurd ha (Nat.not_lt_zero _),
    fun a _ => by simp, ?_⟩
  · show (1 : Matrix _ _ ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  · refine ⟨monotone_const, ?_, fun a => a.elim0, fun a => a.elim0⟩
    simp [Matrix.det_fin_zero]

end GlobalTheory.TypeAsm.BaseFrame

open GlobalTheory.TypeAsm.BaseFrame in
theorem GlobalTheory.TypeAsm.baseFrame_real : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u → N.j = 0 → N.T = Tu D u → N.ist = X.fY →
      ∀ τ : D.what₂.Tau, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) (fun _ => 0)
        (phiV C τ) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) 1 := by
  intro D large₂ X u C hStd N hF hF' hj hT hist τ
  have hv : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := (GlobalTheory.TypeAsm.hostC D large₂ hStd).2.2.1
  rw [hv]
  have hFe : ∀ a : Fin D.R.rS, (F0 X u).e a.castSucc = X.eX a := by
    intro a
    show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
    rw [fv_cast]
    exact congrFun (X.Fu_e u) a
  have hFz : (F0 X u).z = X.zu u := by
    show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
    rw [fv_last]
    exact X.flagZVector u
  have hpe : ∀ a : Fin D.R.rS, phiV C τ (X.eX a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) :=
    fun a => GlobalTheory.CovDom.ModelIso.qi_e X C τ a
  have hpf : ∀ a : Fin D.R.rS, phiV C τ (X.fY a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) :=
    fun a => GlobalTheory.CovDom.ModelIso.qi_f X C τ a
  have hpz : phiV C τ (X.zu u) = zB X (C.Qi τ) u τ := rfl
  obtain ⟨hzW, hzT⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hTz : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hzT]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  refine ⟨⟨GlobalTheory.TypeAsm.GramPf.phiV_add C τ, GlobalTheory.TypeAsm.GramPf.phiV_smul C τ, GlobalTheory.TypeAsm.GramPf.phiV_herm C τ,
    GlobalTheory.TypeAsm.GramPf.phiV_span C τ⟩, hzW, hzW, hTz, ⟨1, normal0_one _ _ _ N.j_le hj _⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hF, hF', hFe, Matrix.one_mulVec, hpe]
    exact ⟨rfl, rfl⟩
  · intro b _
    rw [hist, hpf]
    push_cast
    rfl
  · rw [hF, hFz, hpz]
  · rw [hF', hFz, Matrix.one_mulVec, hpz]

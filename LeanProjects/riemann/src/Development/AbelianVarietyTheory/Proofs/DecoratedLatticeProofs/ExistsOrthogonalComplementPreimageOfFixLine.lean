import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

namespace GlobalTheory.LineFix

set_option maxHeartbeats 1000000 in

theorem exists_emb_of_fix_line : ∀ {D : D7} {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E),
    IsLineVec L ζ → ∀ (b : GA D S₀), (mt S₀ b *ᵥ (fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k)) →
      ∃ a : GA D A, o.emb (a, 1) = b := by
  intro D S₀ A L o ζ hζ b hb
  have hv : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ (fun k => incA D (ζ k)) := by
    funext k
    exact RingHom.map_mulVec (incA D) o.iB ζ k
  have hr := hζ.1
  obtain ⟨k0, hk0⟩ : ∃ k0 : Fin L.rank, ∀ k, k = k0 :=
    ⟨⟨0, by omega⟩, fun k => Fin.ext (by have := k.2; simp only; omega)⟩
  have hz : ζ k0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun k => by rw [hk0 k, h0]; rfl
    rw [this]; simp
  have hu : IsUnit (incA D (ζ k0)) := (isUnit_iff_ne_zero.2 hz).map (incA D)
  have h1 : mt S₀ b ⬝ o.jB = o.jB := by
    have e := hb
    rw [hv, Matrix.mulVec_mulVec] at e
    funext i k
    rw [hk0 k]
    have ei := congrFun e i
    simp only [Matrix.mulVec, dotProduct] at ei
    rw [Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk),
      Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk)] at ei
    exact hu.mul_right_cancel ei
  have hu2 : GlobalTheory.MixModel.adj (mt S₀ b) * (gA S₀ * mt S₀ b) = gA S₀ := GlobalTheory.MixModel.mt_unitary S₀ b
  have h2' : GlobalTheory.MixModel.adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA)) = 0 := by
    calc GlobalTheory.MixModel.adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA))
        = GlobalTheory.MixModel.adj (mt S₀ b ⬝ o.jB) ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA)) := by rw [h1]
      _ = GlobalTheory.MixModel.adj o.jB ⬝ (GlobalTheory.MixModel.adj (mt S₀ b) ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA))) := by
          rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc]
      _ = 0 := by rw [GlobalTheory.MixModel.cancel₃ hu2, o.gram_BA]
  have h2 : o.pB ⬝ (mt S₀ b ⬝ o.jA) = 0 := by
    rw [o.pB_eq]; simp only [Matrix.mul_assoc]; rw [h2', Matrix.mul_zero]
  have h3 : mt S₀ b ⬝ o.jA = o.jA ⬝ (o.pA ⬝ (mt S₀ b ⬝ o.jA)) := by
    calc mt S₀ b ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ b ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ (o.pA ⬝ (mt S₀ b ⬝ o.jA)) := by
          rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc o.jB, h2, Matrix.mul_zero, add_zero]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Mx D A.rank A.rank, mt S₀ b ⬝ o.jA = o.jA ⬝ a₀ := ⟨_, h3⟩
  have h4 : GlobalTheory.MixModel.adj a₀ ⬝ (gA A ⬝ a₀) = gA A := by
    have e : GlobalTheory.MixModel.adj (mt S₀ b ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ b ⬝ o.jA)) = gA A := by
      rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu2, o.gram_AA]
    rw [ha₀, GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA] at e
    exact e
  have e3 : mt S₀ b ⬝ o.jA ⬝ o.pA + mt S₀ b ⬝ o.jB ⬝ o.pB = mt S₀ b ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) := by
    rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
  have e4 : mt S₀ b ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ b := by
    rw [o.sum_eq_one]; exact Matrix.mul_one _
  refine ⟨GlobalTheory.MixModel.ofMat A a₀ h4, GlobalTheory.MixModel.mt_injective S₀ ?_⟩
  have e1 : mt S₀ (o.emb (GlobalTheory.MixModel.ofMat A a₀ h4, 1)) = o.jA ⬝ a₀ ⬝ o.pA + o.jB ⬝ o.pB := by
    rw [OrthDec.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e2 : o.jA ⬝ a₀ ⬝ o.pA + o.jB ⬝ o.pB = mt S₀ b ⬝ o.jA ⬝ o.pA + mt S₀ b ⬝ o.jB ⬝ o.pB := by
    rw [← ha₀, h1]
  rw [e1, e2, e3, e4]

end GlobalTheory.LineFix

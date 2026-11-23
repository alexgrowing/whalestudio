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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.MixModel.HypDec

variable {D : D7}

theorem gram_mt {S : HSp D} (g : GA D S) {k l : ℕ} (x : Mx D S.rank k) (y : Mx D S.rank l) :
    adj (mt S g ⬝ x) ⬝ (gA S ⬝ (mt S g ⬝ y)) = adj x ⬝ (gA S ⬝ y) := by
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)),
    mt_unitary]

theorem exists_emb0_eq_of_fix_jX_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX = d.jX) (hY : mt S g ⬝ d.jY = d.jY) : ∃ b : GA D S₀, d.emb0 b = g := by
  set M := mt S g with hM
  set B := d.p0 ⬝ M ⬝ d.j0 with hB
  have h1 : d.pX ⬝ M ⬝ d.j0 = 0 := by
    rw [pX_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hY, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, gramR_Y0_eq_TI]
  have h2 : d.pY ⬝ M ⬝ d.j0 = 0 := by
    rw [pY_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hX, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, wittDecomp_gram_X_anisotropic]
  have h3 : M ⬝ d.j0 = d.j0 ⬝ B := by
    rw [Matrix.mul_assoc] at h1 h2
    rw [← Matrix.one_mul (M ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero, zero_add, hB]
  have h4 : adj B * (gA S₀ * B) = gA S₀ := by
    have e1 := gram_mt g d.j0 d.j0
    rw [← hM, h3, d.gram_00, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj d.j0),
      ← Matrix.mul_assoc (adj d.j0), Matrix.mul_assoc (adj d.j0), d.gram_00] at e1
    exact e1
  refine ⟨ofMat S₀ B h4, d.ga_ext ?_ ?_ ?_⟩
  · rw [wittDecomp_anisotropicEmbedding_inclX, ← hM, hX]
  · rw [wittDecomp_anisotropicEmbedding_inclAnisotropic, mt_ofMat, ← hM, h3]
  · rw [wittDecomp_anisotropicEmbedding_inclY, ← hM, hY]

end GlobalTheory.MixModel.HypDec

end

import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.BadLog
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BadLogCov

theorem logSum_badPrimes_le_sq : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  intro _
  refine ⟨37, by norm_num, fun D T hT j hj Y e o hY Lb hL hM hE hfr => ?_⟩
  have hQ := hT.pins
  have hM0 : Y.d.l₂.M ≠ 0 := by have := Y.d.l₂.three_le; omega
  have h1 := UpperTheory.KR.sum_log_bad_le D.host.toHostAx Y.d.l₂.M (badPrimes T.Q.H Y.d.l₂) hM0 fun p hp => by
    obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
    refine ⟨hp, ?_⟩
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans hQ.1.1))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · rw [hY.lev.2] at h'
      exact absurd (Nat.dvd_one.1 h') hp.ne_one
  have hrd : Real.log D.host.rd ≤ fieldSz D.host.E := by
    refine le_trans (le_of_eq ?_) (log_rd_le_fieldSz D.host.E)
    unfold Formalism.HC.HostRaw.rd
    rw [Real.log_rpow (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E))]; ring
  have hsum : GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ 37 * Lb := by
    refine le_trans h1 ?_; linarith
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1' := D.R.two_le_m
  have h2' := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hX : Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have a : Lb ≤ (D.R.f : ℝ) * D.R.r * Lb := le_mul_of_one_le_left (by linarith) hfr1
    have b : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * Lb := hL.trans a
    nlinarith
  linarith

end GlobalTheory.BadLogCov

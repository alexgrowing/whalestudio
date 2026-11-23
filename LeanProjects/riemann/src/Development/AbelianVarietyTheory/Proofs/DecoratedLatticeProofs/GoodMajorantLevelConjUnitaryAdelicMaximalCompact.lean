import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevelsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem good_level_conj_stab : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  intro D T T₀ r d b hb hIw l hl
  have hL0 : GlobalTheory.EisCont.IsLevel T (AdelicU.frameLat T) b :=
    ⟨AdelicU.SelfDual.isLattice_frameLat T, AdelicU.SelfDual.isSelfDualAt_frameLat D T, hb⟩
  have hL : GlobalTheory.EisCont.IsLevel T l.L l.c := ⟨hl.1, hl.2.1, hl.2.2⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_adelic_unitary_conj_selfDual_majorant_levels D T (AdelicU.frameLat T) l.L b l.c hL0 hL
  obtain ⟨q, k₀, hk₀, hgq⟩ := hIw g
  have hconj : ConjBy (q : GA D T) l.K (Kmax T b) := by
    intro k
    have h1 : k ∈ l.K ↔ g⁻¹ * k * g ∈ Kmax T b := hg k
    rw [h1, hgq]
    constructor
    · intro h
      have := (Kmax T b).mul_mem (hk₀) ((Kmax T b).mul_mem h ((Kmax T b).inv_mem hk₀))
      simpa [mul_assoc] using this
    · intro h
      have := (Kmax T b).mul_mem ((Kmax T b).inv_mem hk₀) ((Kmax T b).mul_mem h hk₀)
      simpa [mul_assoc] using this
  haveI : Submodule.IsLattice D.host.E l.L := hl.1
  refine ⟨?_, isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _, q, hconj⟩
  intro h
  obtain ⟨q₁, k₁, hk₁, e⟩ := hIw (h * q)
  refine ⟨q₁ * q⁻¹, (q : GA D T) * k₁ * (q : GA D T)⁻¹, ?_, ?_⟩
  · rw [hconj]
    simpa [mul_assoc] using hk₁
  · have : h = (q₁ : GA D T) * k₁ * (q : GA D T)⁻¹ := by rw [← e]; group
    rw [this]; simp [mul_assoc]

end GlobalTheory.RegSch

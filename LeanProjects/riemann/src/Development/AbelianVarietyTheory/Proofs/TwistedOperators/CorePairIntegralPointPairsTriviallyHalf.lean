import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto.IntDatum

theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

theorem finPart_mul_inv_mem {D : D7} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (s : 𝓞 D.host.E)
    (hs : ∀ P ∈ S, s ∉ P.asIdeal) (hs0 : s ≠ 0) : finPart D (e * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  by_contra h
  exact hs PP hPP (((hes PP hPP).2 s hs0).2 h)

end GlobalTheory.CoreOnto.IntDatum

open GlobalTheory.CoreOnto.IntDatum in
theorem GlobalTheory.CoreOnto.IntDatum.psi_int : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)), ∀ a ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf (cA D e) a → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) a) = 1 := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he x₀ hx₀ a ha _
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set N : ℕ := Ideal.absNorm D.host.ccK with hNdef
  have hN : ∀ P ∈ G.pl.W0, ((N : 𝓞 D.host.E)) ∉ P.asIdeal := by
    intro P hP h
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by
      unfold Places.W0 at hP
      simpa using hP
    refine GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces G.pl hv ?_
    rw [← G.pl.under_w hv]
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal
    rwa [map_natCast]
  have hNn : N ≠ 0 := by
    rw [hNdef]
    exact fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hs0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hN0 : ((N : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hNn
  have hα : ((N : 𝓞 D.host.E) : D.host.E) ∈ D.host.AA := by
    have := GlobalTheory.HostClear.absNorm_mem_AA D
    push_cast
    exact this
  have h1 := GlobalTheory.AscFinWit.rat_mem_latO (P := fun _ => True) hS hT x₀ (fun y hy => hx₀ y hy) hα
  have h2 := finPart_mul_inv_mem he (N : 𝓞 D.host.E) hN hs0
  have h3 := GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ h2 _ h1
  refine GlobalTheory.AscFinWit.psi_eq_one (P := fun _ => True) W.ψ_std hS hT ?_ ha
  convert h3 using 1
  have hu : incA D ((N : 𝓞 D.host.E) : D.host.E)⁻¹ * incA D ((N : 𝓞 D.host.E) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hN0, map_one]
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.MixModel.rat, Matrix.map_apply, map_mul]
  linear_combination (GlobalTheory.FinPlLoc.idem D fun _ => True) * e * incA D (x₀ j k) * hu.symm

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartsAll

open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

theorem exists_charts : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  intro D V v w h
  refine ⟨fun hs => (GlobalTheory.NoExcl.chart V h hs).1, fun hns => ?_⟩
  have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
  obtain ⟨w₀, hw₀⟩ := (hI.1 (GlobalTheory.VacCoef.isUnram_host D v)).resolve_left hns
  have h₀ : w₀.under (𝓞 D.host.F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw₀
  obtain rfl : w = w₀ := ((hI.2 w₀ h₀ hw₀).2.2.1 w).1 h
  obtain ⟨-, ⟨c₀, hc₀, -⟩, -, -, H⟩ := hI.2 w h hw₀
  have hfix : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw₀ h
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hfix
  have hv2 : Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
    rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 (by exact_mod_cast h2)
  obtain ⟨⟨ϖ, hU⟩, -⟩ := H c₀ hc₀
  refine ⟨hw₀, GlobalTheory.InertLoc.odd_of_v_two hU hv2, fun c hc => ?_⟩
  obtain ⟨e, he, -⟩ := (H c hc).2 V.rank V.gram (frameLat V) (GlobalTheory.NoExcl.isHermND_gram V) (frameLat_fg V)
    (SelfDual.isLattice_frameLat V).span_eq_top (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨e, he⟩

end GlobalTheory.ChartsAll

import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasuresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

open GlobalTheory.CompanionTheory.SiegelND in

theorem tupOf_act (V : HSp D) (h : GA D V) (X : Fin r → Fin V.rank → AE D) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h X) = mm (mt V h) (tupOf X) := by
  ext i a
  rfl

open GlobalTheory.CompanionTheory.SiegelND in

theorem ip_tupOf (V : HSp D) (X : Fin r → Fin V.rank → AE D) :
    ip V (tupOf X) (tupOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X := by
  ext a b
  exact (GlobalTheory.CompanionTheory.SiegelND.hR_tup V (tupOf X) (tupOf X) a b).symm

open GlobalTheory.CompanionTheory.SiegelND in

def tupE (D : D7) (m r : ℕ) : (Fin r → Fin m → AE D) ≃ᵐ Mx D m r where
  toFun := tupOf
  invFun := tupInv
  left_inv := tupInv_tupOf
  right_inv := tupOf_tupInv
  measurable_toFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupOf.measurable
  measurable_invFun := by
    have := borel_tup (D := D) (m := m) (r := r)
    have : BorelSpace (Mx D m r) := ⟨rfl⟩
    exact continuous_tupInv.measurable

open GlobalTheory.CompanionTheory.SiegelND in

theorem finE {m : ℕ} (ν : Measure (Fin r → Fin m → AE D)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (ν.map (tupE D m r)) := by
  refine ⟨fun K hK => ?_⟩
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D m r) ⁻¹' K = tupInv '' K := by
    ext X
    exact ⟨fun hX => ⟨tupOf X, hX, rfl⟩, fun ⟨y, hy, hyX⟩ => by subst hyX; exact hy⟩
  rw [hs]
  exact (hK.image continuous_tupInv).measure_lt_top

open GlobalTheory.CompanionTheory.SiegelND in

theorem suppE (V : HSp D) (T : Matrix (Fin r) (Fin r) D.host.E) (ν : Measure (Fin r → Fin V.rank → AE D))
    (h : ν {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ = 0) :
    ν.map (tupE D V.rank r) {x | ip V x x ≠ rat T} = 0 := by
  rw [MeasurableEquiv.map_apply]
  have hs : (tupE D V.rank r) ⁻¹' {x | ip V x x ≠ rat T} ⊆
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF D.host.F) D.sp.cm.sig V.gram X = T.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF D.host.F))}ᶜ := by
    intro X hX h0
    apply hX
    change ip V (tupOf X) (tupOf X) = rat T
    rw [ip_tupOf]
    exact h0
  exact measure_mono_null hs h

open GlobalTheory.CompanionTheory.SiegelND in

theorem invE (V : HSp D) (ν : Measure (Fin r → Fin V.rank → AE D)) (h : GA D V)
    (hm : Measurable (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h : (Fin r → Fin V.rank → AE D) → _))
    (hν : ν.map (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h) = ν) :
    (ν.map (tupE D V.rank r)).map (fun x => mm (mt V h) x) = ν.map (tupE D V.rank r) := by
  set e := tupE D V.rank r
  have hg : Measurable fun x : Mx D V.rank r => mm (mt V h) x := by
    have : (fun x : Mx D V.rank r => mm (mt V h) x) =
        e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h ∘ e.symm :=
      funext fun x => (tupOf_act V h (tupInv x)).symm
    rw [this]
    exact e.measurable.comp (hm.comp e.symm.measurable)
  have hc : (fun x : Mx D V.rank r => mm (mt V h) x) ∘ e = e ∘ GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h :=
    funext fun X => (tupOf_act V h X).symm
  rw [Measure.map_map hg e.measurable, hc, ← Measure.map_map e.measurable hm, hν]

end PositivityTheory.Rg.Rsw.L.LFibEx

end

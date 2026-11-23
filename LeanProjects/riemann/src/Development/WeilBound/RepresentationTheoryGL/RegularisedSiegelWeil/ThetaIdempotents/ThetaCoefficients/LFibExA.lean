import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula
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

abbrev thM (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : Matrix (Fin r) (Fin r) D.host.E) :
    Measure (Fin r → Fin V.rank → AE D) :=
  GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = T}

theorem thInt (V : HSp D) (hr : 2 * r < V.rank) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμH : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (T : Matrix (Fin r) (Fin r) D.host.E)
    (hT : ∀ a b, D.sp.cm.sig (T b a) = T a b) (hdet : T.det ≠ 0) (Φ : (Fin r → Fin V.rank → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    Integrable Φ (thM V μH 𝓕 T) := by
  classical
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  let b := Module.finBasis D.host.F D.host.E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf D.host.F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV D.host.F
  have : BorelSpace (Ainf D.host.F) := ⟨rfl⟩
  have : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), BorelSpace (Fv D.host.F v) :=
    fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Ainf D.host.F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf D.host.F hCM.1) b laminf hinf.1 r
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families D.sp.cm.sig hCM V.gram hJ (Fv D.host.F v)
    (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv D.host.F v) b (lam v) (hlam v).1 r
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (thM V μH 𝓕 T) 1
      (minf (hermOf (Ainf D.host.F) D.sp.cm.sig T hT)) (fun v => m v (hermOf (Fv D.host.F v) D.sp.cm.sig T hT)) :=
    GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero D.host.F D.host.E D.sp.cm.sig hCM r V.rank V.gram hJ (by omega) T hT hdet _ b laminf lam hinf hlam
      μH 𝓕 hμH h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_finite_sum_of_products D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b Φ hΦ
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_measure_eventually_standard D.host.F D.host.E V.rank r _ b _ 1 _ _ hEu
  have hu : ∀ (R : Type) [CommRing R] [Algebra D.host.F R],
      IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det := by
    intro R _ _
    have h : (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R D.sp.cm.sig T hT).1.det = HeckeCharacterZeroLocus.SiegelWeilU.inclR R T.det :=
      ((HeckeCharacterZeroLocus.SiegelWeilU.inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR R)
  have hP : ∀ i, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i)) (thM V μH 𝓕 T) := by
    intro i
    obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b laminf hinf
      minf hminf _ (hu _) (φ i) (hφ i)
    have hfin := fun v => GlobalTheory.T.local_gram_fibre_measure_standard_volume D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr _ b v (lam v)
      (hlam v) (m v) (hm v) (hermOf (Fv D.host.F v) D.sp.cm.sig T hT) (hu _) (A i v) (hA i v).1 (hA i v).2
    exact (hS₁ (S ∪ S₁) Finset.subset_union_right (φ i) hφm hφi.self_of_nhds (A i) (fun v => (hfin v).1)
      (fun v => (hfin v).2) (fun v hv => hAl i v fun h => hv (Finset.mem_union_left _ h))).1
  have hΦe : Φ = fun X => ∑ i, GlobalTheory.CompanionTheory.SiegelND.Coef.pureN (φ i) (A i) X := funext hsum
  rw [hΦe]
  exact integrable_finsetSum _ fun i _ => hP i

end PositivityTheory.Rg.Rsw.L.LFibEx

end

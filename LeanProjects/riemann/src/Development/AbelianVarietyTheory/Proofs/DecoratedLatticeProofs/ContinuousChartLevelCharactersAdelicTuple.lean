import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBadPrimeOverChartBadPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlaceStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

namespace GlobalTheory.AdForm.ChiCont

set_option maxHeartbeats 2000000 in

theorem chi_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ) := by
  intro B X I hI hP l Z u a Ch A hA i hi β
  obtain ⟨n, hn, hfin⟩ := hA.fin i hi β
  let Vs : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) :=
    {v | ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)}
  have hVs : Vs.Finite := by
    have e : Vs = ⋃ P : SBof I a, {v | Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)} := by
      ext v; simp [Vs]
    rw [e]
    refine Set.finite_iUnion fun P => Set.Subsingleton.finite ?_
    intro v hv w hw
    exact HeightOneSpectrum.ext (hv.trans hw.symm)
  have hbad : ∀ v ∈ A.bad i, v ∈ Vs := fun v hv => GlobalTheory.T.exists_badPrime_over_chart_bad_place I hI hP l Z a v (hA.bad_le i hi v hv)
  have hker := GlobalTheory.T.levelCharacter_trivial_near_one_of_local_bad_places (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi)
    (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev Vs hVs hbad (by
    rintro v ⟨P, hv⟩
    obtain ⟨N, hN⟩ := GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace I hI hP l Z a (B.T u) i hi (A.bad i) (A.K i hi β).lev n hn hfin P v hv
    have h2 := GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) ((I.rec7 l Z).R.N i) N
      (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    exact h2.mono fun w hw x hx hxw => hN x hx w hw hxw)

  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  haveI : IsTopologicalGroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let Φ : A.U i β →* GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    (GlobalTheory.ClassSumLevel.finGLHom ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi)).comp (A.U i β).subtype
  have hΦc : Continuous Φ := (GlobalTheory.ClassSumLevel.continuous_finGLHom _ _).comp continuous_subtype_val
  have ht : Tendsto Φ (nhds 1) (nhds 1) := by
    have := hΦc.tendsto 1
    rwa [map_one] at this
  have hev : ∀ᶠ g in nhds (1 : A.U i β), (1 : ℂˣ) = A.chi i β g := by
    filter_upwards [ht.eventually hker] with g hg
    obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
    rw [hA.chi i hi β g κ hκ]
    exact (hg κ (Units.ext (hκ.trans rfl))).symm
  have hχ : Continuous (A.chi i β) := by
    refine continuous_of_continuousAt_one (A.chi i β) ?_
    exact continuousAt_const.congr hev
  exact Units.continuous_val.comp hχ

end GlobalTheory.AdForm.ChiCont

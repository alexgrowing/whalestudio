import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.GoodModUnr

open GlobalTheory.IdemSupport

variable {D : D7}

theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} {χ : (AE D)ˣ →* Circle} (h : GlobalTheory.Hk3.UnrPl w χ) :
    GlobalTheory.LFun.UnrAt χ w := by
  intro u hu
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  have hd := (of_isPrimeIdem hΦ hp).1
  have hee : e * e = e := delta_idem hΦ hd
  have hfe : f * e = e := by
    rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
    · have ho : e * cA D e = 0 := hi.1.2.1
      linear_combination hee + ho
    · exact hee
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w u).1 hu
  have hg : e * ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) + (1 - e) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) :=
    GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd (GlobalTheory.LFun.EulerTie.finComp_locIdele_self w u)
  have hx : f * (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1 := by
    linear_combination (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) * hfe + (1 - f) * hg
  have i1 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u).2 h1
  have i2 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u⁻¹).2 h2
  rw [map_inv] at i2
  have := h e f hp _ hx i1 i2
  exact (congrArg Circle.toUnits this).trans (map_one _)

theorem good_of_ne {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) (hv : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.Hk3.Good R t w := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  intro PP hPP
  have key : PP.under (𝓞 D.host.F) ≠ v := by
    intro hu
    obtain ⟨e, f', hp⟩ := exists_isPrimeIdem hΦ PP
    obtain ⟨-, ε, hε, hf'⟩ := of_isPrimeIdem hΦ hp
    obtain ⟨ε', hε', rfl⟩ := hf
    rw [hu] at hε
    exact hv PP hPP e f' hp (by rw [hf', placeIdem_unique hε hε'])
  refine ⟨fun h => key (h ▸ hw), fun h => key ?_⟩
  rw [← hw, (isConjPl_iff PP w).1 h, under_cP]

theorem chrTh_unrAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hv w hw
  obtain ⟨he, hm⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hL.lev t w (good_of_ne R t hf hv hw)
  have a := unrAt_of_unrPl (hm ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega))
  have b := unrAt_of_unrPl he
  exact ⟨a, a.mul b.inv⟩

end GlobalTheory.GoodModUnr

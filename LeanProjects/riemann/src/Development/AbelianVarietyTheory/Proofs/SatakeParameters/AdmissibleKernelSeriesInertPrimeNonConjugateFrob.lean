import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBasesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem exists_beFam_evenConditionsInert_of_kerEnt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3
  have hOrb := (Formalism.MainNotions.DIV.Inh.orbit_admissible_of_split_bound D h3).1
  have key : ∀ w : D.what₂.places.Pl, ∃ (e : ℂ_[D.what₂.places.resChar w])
      (b : MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]),
      ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
      ‖e‖ = 1 ∧ BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) b ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
        ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → ∀ R, OrbitPlaces.IsReps D (D.what₂.places.resChar w) R →
          OrbitPlaces.ThetaExpansionAllPlaces D (D.what₂.places.resChar w) R e (fun _ => -1) (fun _ => b) (stdSer D (t.ent.lam w) (fun _ => 1) P P' G) := by
    intro w
    by_cases hc : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)
    · have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
      have hH := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) hO.five
        (hc.imp_left And.left)
      obtain ⟨e, b, he, hb, hB⟩ := GlobalTheory.T.normalisedFamily_standardBases_integrality_alt D t.cc t.δ t.B t.χ _ (t.ent.lam w) hH hO (hc.imp_left (And.imp_right HEv.ne_zero))
      exact ⟨e, b, fun _ => ⟨he, hb, hB⟩⟩
    · exact ⟨1, 0, fun h => absurd h hc⟩
  choose ep be hbe using key
  refine ⟨ep, fun w _ => be w, ?_, ?_⟩
  · intro w hc
    obtain ⟨he, hb, -⟩ := hbe w hc
    exact ⟨he, fun _ => hb⟩
  · intro u μ w hLev hc R hR
    obtain ⟨he, hb, hB⟩ := hbe w hc
    have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
    refine ⟨⟨he, fun _ _ => Or.inr rfl, fun _ _ => GlobalTheory.T.standard_series_b_conditions_large_prime _ _ _ hO.five hO.two hO.even hb⟩, ?_⟩
    intro i hi _ c c'
    have hAdPl : Formalism.L2.Ker.AdPl D w := by
      rcases hc with h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h)
    obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hAd w hAdPl u μ hLev
    have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLev i hi c c'
    have hS : ∀ j, j ≤ D.R.m → ∀ c, StdBases D (t.ent.lam w) ((t.O u μ).lat j c).1 (Pm j c) := fun j hj c =>
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j c).2.1 (fun τ => hBas j hj c τ)
        (fun τ τ' h => hConj j hj c τ τ' h)
    show OrbitPlaces.ThetaExpansionAllPlaces D _ R (ep w) (fun _ => -1) (fun _ => be w) (t.ent.Th u μ w i c c')
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact hB _ _ _ _ _ _ hcomb.1 (hS i hi.le c) (hS (i + 1) hi c') _ hcomb.2 R hR

end GlobalTheory.KerStd

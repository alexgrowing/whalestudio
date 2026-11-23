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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.B0StandardSeriesAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
import Development.AutomorphicArithmetic.OrbitLabellings.LatticePairsOddDegreeIsometric

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.Ggeo

theorem frobeniusConjugation_conditions_adaptedKernelDatum_alt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3 ep be sg
  have main : ∀ u μ (w : D.what₂.places.Pl), LevFree Y u μ w → IsResidueClassZero D (D.what₂.places.resChar w) → ∀ i < D.R.m, ∀ c c',
      ∀ Q : MvPowerSeries (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w] → Prop,
      (HostAt t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) → 5 ≤ D.what₂.places.resChar w →
        ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
          (P : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
          (P' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E),
          admitted D (D.R.N i) (D.R.N (i + 1)) L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
          ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → Q (stdSer D (t.ent.lam w) (fun _ => 1) P P' G)) →
      Q (t.ent.Th u μ w i c c') := by
    intro u μ w hLF' hC i hi c c' Q hQ
    have hprime : (D.what₂.places.resChar w).Prime := Fact.out
    have h5 : 5 ≤ D.what₂.places.resChar w := (DIV.Inh.orbit_admissible_of_split_bound D h3).2 _ hprime hC
    have hAdPl : Formalism.L2.Ker.AdPl D w := Or.inl hC
    obtain ⟨Pm, hB, -, hConj, hTh⟩ := hAd w hAdPl u μ hLF'
    obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLF' i hi c c'
    have hHA := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) h5 (Or.inl hC)
    have hS : StdBases D (t.ent.lam w) ((t.O u μ).lat i c).1 (Pm i c) :=
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat i c).2.1 (fun τ => hB i hi.le c τ)
        (fun τ τ' h => hConj i hi.le c τ τ' h)
    have hS' : StdBases D (t.ent.lam w) ((t.O u μ).lat (i + 1) c').1 (Pm (i + 1) c') :=
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat (i + 1) c').2.1 (fun τ => hB (i + 1) hi c' τ)
        (fun τ τ' h => hConj (i + 1) hi c' τ τ' h)
    have key := hQ hHA h5 _ _ _ _ hAdm hS hS' _ hComb
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact key
  refine ⟨fun u μ w hLF hC hP0 i hi _ c c' => ?_, fun u μ w hLF hC i hi _ c c' => ?_⟩
  · exact main u μ w hLF hC i hi c c' (OrbitPlaces.ThetaExpansionRealPlaces D (D.what₂.places.resChar w)) fun hHA h5 =>
      GlobalTheory.T.thetaExpansionRealPlaces_stdSer_of_adm' D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC hP0 _ _
  · have hodd : Odd (nP D (D.what₂.places.resChar w)) := by
      have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun h => by
        have h1 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := hC.1
        have h2 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal := h
        rw [h1] at h2; cases h2
      unfold nP
      rw [if_neg hs]
      exact hC.2.1
    exact main u μ w hLF hC.1 i hi c c' (OrbitPlaces.EvenConditionsAllReal D (D.what₂.places.resChar w)) fun hHA h5 =>
      UpperTheory.lattice_pairs_odd_degree_isometric D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC.1 hodd _ _

end GlobalTheory.Ggeo

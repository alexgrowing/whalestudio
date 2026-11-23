import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZeroContentPlacesIffOverOfNonvanishing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.W1idxUnionW1jwFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDualLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtendeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataDefiniteLiftLatticeBaseChangeStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem exists_hom_of_range {K K' : Type} [Field K] [Field K'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (h : Set.range σ ⊆ Set.range σ') :
    ∃ φ : K →+* K', ∀ x, σ' (φ x) = σ x := by
  choose g hg using fun x => h ⟨x, rfl⟩
  exact ⟨{ toFun := g
           map_one' := σ'.injective (by rw [hg, map_one, map_one])
           map_mul' := fun a b => σ'.injective (by rw [map_mul σ', hg, hg, hg, map_mul])
           map_zero' := σ'.injective (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => σ'.injective (by rw [map_add σ', hg, hg, hg, map_add]) }, hg⟩

set_option maxHeartbeats 4000000 in

theorem extendedData_nonzero_index_places_correspond : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (GlobalTheory.T.liftFormsLattice_definiteLattice_baseChange_extended h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.extendedData_definiteLiftLattice_baseChange h1 h2 h3 h4 h5 h6 h7)) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ hIJ B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt v v' hB
  have hm : (w.st Z).toD7.R.m = (w'.st Z').toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1.symm
  obtain ⟨φ, hφ⟩ := exists_hom_of_range (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL hE.2.2.2
  have hok := hHL.ok.ok2
  refine mem_zeroContentPlaces_iff_over_of_nonvanishing z z' hm (fun j j' hj P P' hPP => ?_) v v' hB
  have hP : ∀ (x : 𝓞 (w.st Z).toD7.what₂.LL) (x' : 𝓞 (w'.st Z').toD7.what₂.LL), φ (x : (w.st Z).toD7.what₂.LL) = (x' : (w'.st Z').toD7.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal) := fun x x' e => hPP x x' (by rw [← e, hφ])
  have hT : Submodule.IsLattice (w.st Z).toD7.what₂.LL (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) := Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr
  have hH : IsUnit (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).det := Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr
  obtain ⟨G, hG1, hG2, hG3⟩ := hIJ.1 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨N, hN1, hN2, hN3⟩ := hIJ.2 B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  refine nzAt_iff_of z z' j j' P P' ?_ ?_
  · have k := GlobalTheory.T.lattice_index_nonzero_iff_under_field_map _ _ φ _ _ G hG1 P P' hP ((s0Of z.R z.F).M j)
      (Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (hHL.mLat j).fg (hT.fg.map _)
    rw [← hG2, ← hG3] at k
    exact k
  · have k := GlobalTheory.T.lattice_index_nonzero_iff_under_field_map _ _ φ _ _ N hN1 P P' hP _ _ hT.fg (GlobalTheory.Mem.NonzeroPlacesOverPrimes.dual_fg _ hH _ hT)
    rw [← GlobalTheory.T.hermitianDualLattice_baseChange _ _ φ _ _ N hN1 _ _ hN3 hH _ hT, ← hN2] at k
    exact k

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBelowOfRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeedsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharEqOfOverOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.UntwSat

theorem stepW_seed_fixed : StepW Pinned fun K B f T _ =>
    (↑(NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre) : Set ℕ) ⊆ ↑T.pl ∧ ∀ px : PreX B.toPre,
      (∃ F₀, SeedW K B.toPre f B.KsC F₀ px Set.univ ⊤) → ∃ F₀, SeedW K B.toPre f B.KsC F₀ px ↑T.pl B.fixedCoefficientFieldInComplex := by
  refine evG_all fun K => ?_
  choose S S₁ hS₁ hS using GlobalTheory.T.exists_uniform_normalisedAdelicSeeds K
  refine ⟨fun P f F => S₁ P f F, fun P f F _ => S P f F ∪ NonzeroPlacesOverPrimes.forcedContentSupportPrimes K P, fun _ _ _ _ _ => ∅,
    fun _ _ _ _ _ => ∅, fun P f F => hS₁ P f F, by simp, ?_⟩
  intro B f T _ hHas hP _ _ _ _ w _
  refine ⟨fun p hp => hP (Finset.mem_union_right _ hp), fun px hs => ?_⟩
  obtain ⟨F₀, h⟩ := hS _ _ _ px hs
  refine ⟨F₀, h.mono ?_ ?_⟩
  · intro p hp
    exact hP (Finset.mem_union_left _ hp)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact hHas.1 z hz

theorem isBaseEnlargementFixedCoefField_of_same_fields {B₀ B : Base} (hP : B₀.toPre = B.toPre) (hKs : B₀.KsC = B.KsC) (hLL : B₀.LLC ≤ B.fixedCoefficientFieldInComplex) : Enl0 B₀ B := by
  refine ⟨hP.symm, ?_, ?_, ?_⟩
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hKs
    simp only [Base.KsC, IntermediateField.coe_map] at this
    exact this.symm
  · rintro _ ⟨x, -, rfl⟩
    exact (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  · rintro _ ⟨x, rfl⟩
    exact (B.mem_LLC).1 (B.fixedField_le_coefficientField (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩)))

theorem dat_saturated_of_untw : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 →
    StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧
        DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧
        (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧
        ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  intro hG hDS hHL hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hHLw : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
      HoldsL z.R z.F := hHL
  refine (((((hP.and hDS).and hHLw).and hDE).and GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep).and stepW_seed_fixed).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨⟨⟨pin⟩, hDS'⟩, hHL'⟩, hDE'⟩, G, hG2⟩, hf0, hsd⟩ := H
  intro hT
  obtain ⟨Z, rfl, hGT, hGA, hKap⟩ := exists_lt_grpTrue hG w hO pin.hX G
  have hVol := (hG2 Z.W Z.V Z.S Z.N).1
  obtain ⟨z₁, hF₁⟩ := hDS' Z pin.hX hGT hGA hVol
  have hL₁ := hHL' Z pin.hX _ z₁ hGT hGA hF₁.1 hF₁.2.1
  have hs : SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex w.px Set.univ ⊤ :=
    ⟨B, f, T, w, Z, pin.hX, _, z₁, rfl, HEq.rfl, rfl, rfl, HEq.rfl, ⟨pin⟩, hGT, hGA, hF₁, hL₁, fun _ _ => trivial, le_top⟩
  obtain ⟨F₀, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, hB₀, hf₀, hKs, -, hpx, hpin₀, hGT₀, hGA₀, hFine₀, hHL₀, hW₀, hLL⟩ :=
    hsd w.px ⟨_, hs⟩
  have hE : Enl0 B₀ B := isBaseEnlargementFixedCoefField_of_same_fields hB₀ hKs hLL
  obtain ⟨z', hFine', hExt⟩ := hDE' B₀ f₀ T₀ w₀ hE hf₀.symm hpin₀ hpx.symm Z₀ hX₀ Wt₀ z₀ hGT₀ hGA₀ hFine₀ hHL₀ Z pin.hX hGT hGA hVol
  have hsub : ∀ x : (w₀.D Z₀).what₂.LL, ∃ y ∈ (w.D Z).LL0, (w.D Z).what₂.embLL y = (w₀.D Z₀).what₂.embLL x :=
    fun x => (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  refine ⟨Z, pin.hX, z', hG2, hGT, hGA, hKap, hFine', ?_, ?_, ?_⟩
  · intro v' hv'
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').1 hv' with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v'
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v' hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').2 (Or.inl h))
      have hr : B.places.resChar v' = B₀.places.resChar v := Untw.resChar_of_below hB
      have hm : B₀.places.resChar v ∈ (T.pl : Set ℕ) := hW₀ v hv
      rw [hr]
      exact hm
    · exact hf0 (NonzeroPlacesOverPrimes.resChar_mem_f0Primes K B f T w Z v' h)
  · intro v _
    have e := congrArg (fun T' : TwDat B => T'.psi v) hT
    exact e.trans rfl
  · intro v₁ v₂ hov hv₁
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).1 hv₁ with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v₁
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v₁ hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).2 (Or.inl h))
      have hB₂ := GlobalTheory.T.placesOverFixedField_same_coefficient_place (w₀.D Z₀) (w.D Z) hsub v v₁ v₂ hov hB
      have hv₂ := (hExt.W1 v v₂ hB₂).1 hv
      rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).1 hv₂ with h₂ | h₂
      · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inl h₂)
      · obtain ⟨j, y, -, hne⟩ := h₂
        exact absurd rfl hne
    · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inr (GlobalTheory.Mem.SatForced.mem_W1F_of_overOne K (w.D Z) v₁ v₂ hov h))

end GlobalTheory.Mem.R3.Rw.UntwSat

end

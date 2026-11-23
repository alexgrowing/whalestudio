import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsWithoutBlockNodupParametersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualsEqTateDualsAtEnlargementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockComplementIsSubAtEnlargementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldEnlargementLocChiCyclotomicStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jumpIn_of_reads : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  intro D L C₀ i w hw C r ρ π ε κ hR hA hT hinc hc hcW hcr hS hτ
  have hε := GlobalTheory.T.coefficientFieldEnlargement_locChi_cyclotomic i w hw C hinc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedDuals_eq_tateDuals_at_enlargement i w hw C r ρ π hε
  have hO := goodO_finExt_integers (D.nd.l i) C.LL
  haveI : IsTopologicalRing ↥C.LL.1 := hO.2.2.2.1
  have hsub := GlobalTheory.T.block_complement_isSub_at_enlargement i w hw C r ρ π hS
  have hF : Formalism.MainNotions.LocalSituation.fontCore (Br.PD D.loc D.nbr i w hw) := hA (D.nd.l i) (D.nbr i w hw).Kw
  let A : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := Fin D.R.r → ↥C.LL.1
      ρ := matRep (C.loc (WpO D.nd i ρ π))
      cont := fun x => by
        change Continuous fun g => (C.loc (WpO D.nd i ρ π) g).mulVec x
        exact hcW.matrix_mulVec continuous_const }
  have hcrW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (WpO D.nd i ρ π))) :=
    GlobalTheory.CrysSub.isCrys_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) hF hO A
      (fun _ : Unit => C.loc (rTwO D.nd i r π)) (fun _ => hc π) hsub (fun _ => hcr π)
  have dual := fun x => GlobalTheory.T.tateDual_matrixRep_continuous_crystalline (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (rTwO D.nd i r x)) hT (hc x) (hcr x)
  have dualW := GlobalTheory.T.tateDual_matrixRep_continuous_crystalline (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (WpO D.nd i ρ π)) hT hcW hcrW
  have uniq : ∀ τ g g', Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g →
      Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g' → g = g' := fun τ g g' hg hg' =>
    (GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host (D.nbr i w hw).Kw C.LL (Br.cEw D.nbr i w hw) κ τ).unique hg hg'
  refine ⟨fun x => ?_, fun x => ?_, fun x τ g hg => ?_, ?_, fun τ g hg u => ?_⟩
  · rw [h1 x]; exact (dual x).1
  · rw [h1 x]; exact (dual x).2
  · obtain ⟨g', hg', hj, -⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    exact fun a ha => hj x a ha
  · rw [h2]; exact dualW.2
  · obtain ⟨g', hg', -, hm⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    refine (hm u).trans ?_
    have hnd := GlobalTheory.T.jT2_hcAt_nodup_of_roomy L C₀ (liftIdx D i) g (pos ε g) hR
    split_ifs with hu
    · rw [Multiset.count_eq_one_of_mem hnd hu]; rfl
    · rw [Multiset.count_eq_zero_of_notMem hu]; rfl

end GlobalTheory.HTW.Rec

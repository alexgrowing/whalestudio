import Formalism.SharpRestriction.LevelLetterCocycles.RestPt
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleDistinctConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecompositionStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.RestPtAssembly

theorem chiRat_isCrys (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (h1 : 1 ≤ c)
    (h2 : c ≤ D.R.t) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) := by
  have h0 := ((GlobalTheory.BlockCrys.chiRatioCrysAt D i w hw) c h1 h2).2
  have hM : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))) := by
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ (LinearEquiv.funUnique (Fin 1) _ _).symm
      (fun g x => ?_) h0
    funext a
    rw [Subsingleton.elim a 0]
    have e1 : Br.loc D.nbr i w hw (chiRatO D.nd i c) g 0 0 =
        ((Br.locChi D.nbr i w hw (GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatio D i c) g : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
      change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) =
        (D.nbr i w hw).toLL ((GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatio D i c (decS D.nd w (Br.iota D.nbr i w hw g)) :
          (D.nd.O i)ˣ) : D.nd.O i)
      rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    change _ = (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec (fun _ => x) 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, e1]
    rfl
  exact GlobalTheory.CrysCoef.isCrys_inclusion _ (D.loc (D.nd.l i)) _ _ _ C.le _ _ hM

end GlobalTheory.RestPtAssembly

open GlobalTheory.RestPtAssembly in

theorem GlobalTheory.restPt_of_ptFam : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (r i) (ρ i) π := by
  intro hF D r ρ hP h41 hO i hl π hπ
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := by
    have hx := hπ
    rw [D.Z_tie]
    rw [D.Zgood_tie] at hx
    exact hx.1
  obtain ⟨hrho, hss, hblock, hdec⟩ := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D r ρ hP i π hZ
  obtain ⟨hshape, heps⟩ := GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation D i
  have hG2 := ((h41 i).2.2 _ (hP.good i)).2.1
  have hX := GlobalTheory.T.coefficient_extension_decomposition hF D i (r i) (ρ i) π (hP.good i) hG2 hg0 hg1 hdec
  exact
    { ng0 := hg0
      ng1 := hg1
      good := hP.good i
      chi1 := fun w hw C => (hX w hw C).1
      block := hblock
      chi := fun w hw C c h1 h2 => chiRat_isCrys D i w hw C c h1 h2
      g3 := GlobalTheory.abs_irreducible_distinct_constituents D h41 hO i _ (hP.good i)
      cont := hP.cont i π
      rho := hrho
      ss := hss
      eps := heps
      shape := hshape }

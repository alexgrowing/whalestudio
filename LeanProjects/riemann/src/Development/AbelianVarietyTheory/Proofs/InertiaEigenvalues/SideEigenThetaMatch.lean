import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFactsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCuspStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMonoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenHeckeMatchStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DutiesOfLargeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarevStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty

theorem large_and_duties_of_large_rings : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → BuiltEx A M C tp.tup → EvO A M C tp.tup (fun D' => (SumRepresentations.hypO D' → SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D') → EvO A M C tp.tup (fun D' => Large D' ∧ Duties D') ∧ ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ Built A M C tp.tup big L ∧ Large (withLoc L) ∧ Duties (withLoc L) := by
  intro hCheb D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx hO
  have hStd : HeckeStdPlain := GlobalTheory.T.heckeDoubleCosetOperators_standardFacts

  have hConj := fun P₁ P₂ => (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup P₁ P₂).1
  have hMono := fun P₁ P₂ => (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup P₁ P₂).2.1

  have E1 : EvO A M C tp.tup SumRepresentations.hypO :=
    GlobalTheory.T.side_eigen_rationality hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh

  have E2 : EvO A M C tp.tup GlobalTheory.SplitCoef.OSplit := by
    obtain ⟨big, hbig⟩ := GlobalTheory.T.side_multiplicity_cusp D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
    refine ⟨big, fun L hB => ?_⟩
    obtain ⟨Sp, ⟨hA⟩, -⟩ := hB
    exact hbig L Sp hA

  have E3 : EvO A M C tp.tup (fun D' => ∀ i, ZDecomp D'.nd i) :=
    hMono _ _ (fun D' h => GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev hCheb D' h.2) hO
  have E4 : EvO A M C tp.tup (fun D' => SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') :=
    hMono _ _ (fun D' h => h.2.1 h.1) (hConj _ _ E1 hO)

  have E5 : EvO A M C tp.tup TakenAll :=
    GlobalTheory.T.side_eigen_hecke_match hCheb hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx
      (hMono _ _ (fun D' h => ⟨h.1.1, h.2.1, h.2.2⟩) (hConj _ _ E4 (hConj _ _ E2 E3)))
  have EL : EvO A M C tp.tup Large :=
    hMono _ _ (fun D' h => ⟨h.1, h.2.1, h.2.2⟩) (hConj _ _ E1 (hConj _ _ E2 E5))
  have ELD : EvO A M C tp.tup (fun D' => Large D' ∧ Duties D') :=
    hMono _ _ (fun D' h => ⟨h.1, GlobalTheory.T.duties_of_large_of_cheb hCheb D' h.1 h.2.1 h.2.2⟩) (hConj _ _ EL E4)
  refine ⟨ELD, fun big₀ => ?_⟩
  obtain ⟨big, L, hsub, hB, hP⟩ :=
    (GlobalTheory.T.eventually_conjunction_mono D cf jE A M C tp.tup (fun D' => Large D' ∧ Duties D') (fun _ => True)).2.2.1 hEx ELD big₀
  exact ⟨big, L, hsub, hB, hP.1, hP.2⟩

end GlobalTheory.CoefDuty

end

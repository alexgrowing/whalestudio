import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReading
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisReps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
end GlobalTheory.TripInhab
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
theorem isTriple_of_sideB_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → _root_.GlobalTheory.EigTie.ResTiedAlt D Rw → _root_.GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisRepsAlt D → D.nexp.sig_all → _root_.GlobalTheory.Triple.IsGaloisTriple D := by
  intro hCheb hArt D cf Rw low Pq S hL eig θ Bs Sb hSb hks hT hG hCS hV hroot hstar hET hEO hRP hRT hGR hall
  obtain ⟨art, ha⟩ := hArt D.host.E D.nd.Om
  refine ⟨cf, art, ha, fun i hi b => ?_,
    fun i _ s => GlobalTheory.T.twistTriple_eigenvector_in_good_part D cf Rw low Pq S hL eig θ Bs Sb hSb hks hEO i s, hall⟩
  obtain ⟨ρ, w, red, hind, hres⟩ := hRT.exists_reading hstar hi b
  have hc : IsChars cf art ρ := GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings hCheb hArt D cf Rw low Pq S hL eig θ Bs hT hG hCS hV hroot art ha i b ρ
  refine ⟨ρ, hc, fun s hs => ?_⟩
  subst hs
  obtain ⟨hocc, hgood, hspec⟩ := Bs.rhoS i s
  obtain ⟨π, hpar⟩ := hRP _ (D.ntw.jS_range i s).1 (D.ntw.jS_range i s).2 _ hocc hgood
  obtain ⟨r, hr⟩ := hGR π hpar.1.csd hpar.1.ralg (D.ntw.l i) ρ.ι
  obtain ⟨ν, n, hν⟩ := exists_shift ha hV ρ
  have hR1 := hspec π hpar.1.csd hpar.1.ralg hpar.2 ρ.κ ρ.ι ρ.κ_alg (fun x => ρ.read x)
  have hR2 := _root_.GlobalTheory.TripInhab.isRepOf_twGL_of_isGal ha hCS ρ hr hν
  obtain ⟨A, hA⟩ := GlobalTheory.HeightCounting.FitRho.conj_of_isRepOf D ρ.ι _ _ (GlobalTheory.ChebSplitDense.chebSplit_nd hCheb D) _ _ hR1 hR2
  have hhk := GlobalTheory.TwInputs.HEig.hEig_eq_heckeVal D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hpar
  refine _root_.GlobalTheory.Triple.isTripleAt_of_conj_alt hgood hocc hpar.1 hr ⟨n, hν⟩ A (fun g => ?_) hhk hind
    (hres.2.2 _ π r hgood ⟨_, (D.ntw.jS_range i s).1, (D.ntw.jS_range i s).2, hocc⟩ hpar hr)
  have := congrArg (fun M : GL (Fin D.R.r) (Qbar (D.ntw.l i)) => (M : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))) (hA g)
  simp only [Units.val_mul, GlobalTheory.TwistAbove.twGL_val, Matrix.mul_smul, Matrix.smul_mul] at this
  rw [Units.val_mul, Units.val_mul]
  exact this
end GlobalTheory.TripInhab
end
end

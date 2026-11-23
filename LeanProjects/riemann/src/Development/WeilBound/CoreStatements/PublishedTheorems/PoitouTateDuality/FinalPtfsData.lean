import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

structure FoundData (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) (l r : ℕ) [Fact l.Prime] (ζ : AlgebraicClosure ℚ)
    (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M) where
  e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
    galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))
  he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
    (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
    ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
        AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)
  ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 Kf.1))), AlgebraicClosure ℚ →ₐ[Kf.1]
    AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
  ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) (Av v)
  hev_cont : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm
  hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
    gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ
  hιs : ∀ (v : S) σ x, ιs ⟨v.1, Finset.mem_coe.2 v.2⟩
    (((ev v σ : Dec (F := Kf.1) (Av v)) : G Kf.1 (AlgebraicClosure ℚ)) x) =
      σ (ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ x)
  A : Rep.{0} (ULift.{0} ℤ)
    (galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
  isDiscrete : IsDiscreteRep A
  eM : M ≃+ A.V
  hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)
  eD : TDual (ZMod (l ^ r)) M ≃+
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).V
  hD : ∀ g f, eD (twDual μ ρ g f) =
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).ρ (e g) (eD f)
  hDζ : ∀ f m, ((((Additive.toMul ((eD f : A.V →ₗ[ULift.{0} ℤ] _) (eM m)) :
      rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
        (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
          AlgebraicClosure ℚ) = ζ ^ (f m).val

end PositivityTheory.Lit1.PTN

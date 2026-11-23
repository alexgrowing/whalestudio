import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.WhittakerSupportTildeOf
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCuspTh :
    CuspTh := by
  intro E _ _ _ n w σ
  let σ' : SmIrr (GLw n w) :=
    { V := σ.V
      ρ := σ.ρ.comp (invT n (w.adicCompletion E))
      smooth := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isSmooth_comp_invT σ.smooth
      irred := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isIrreducible_comp_invT σ.irred }
  refine ⟨σ', LinearEquiv.refl ℂ _, fun g g' v h => ?_, fun hc => ?_⟩
  · have hg : g' = invT n (w.adicCompletion E) g := Units.ext h
    subst hg
    show σ.ρ (invT n _ (invT n _ g)) v = σ.ρ g v
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
  · have h2 := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isCuspidal_comp_invT (ρ := σ'.ρ) hc
    have h3 : σ'.ρ.comp (invT n (w.adicCompletion E)) = σ.ρ :=
      MonoidHom.ext fun g => by
        show σ.ρ (invT n _ (invT n _ g)) = σ.ρ g
        rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
    rwa [h3] at h2

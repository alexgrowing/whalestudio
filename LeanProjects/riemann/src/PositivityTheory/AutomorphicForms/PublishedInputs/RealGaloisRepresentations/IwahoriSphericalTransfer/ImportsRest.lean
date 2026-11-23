import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.TemperedTransport.main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (x : WD h) (x' : WD h'), WDRel (RingEquiv.refl Ω) x x' → ∀ s : ℝ, (x'.lpTw s).tempered → (x.lpTw s).tempered := by
  intro F Ω _ _ _ _ _ K _ _ _ _ A v w h h' j i hP x x' hx s ht
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i hP
  obtain ⟨c, hc, hdeg, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i hP
  have hx2 : WDRel (RingEquiv.refl Ω) (x.lpTw s) (x'.lpTw s) := by
    rw [hS, hTw, (hS x x').mp hx]
  obtain ⟨n, b, b', hb, hb', hN, hρ⟩ := hx2
  rw [← hb, WD.tempered_mk]
  rw [← hb', WD.tempered_mk] at ht
  intro φ hφ
  have h1 : b.ρ φ = b'.ρ (c φ) := hρ φ (c φ) ((hc φ (c φ)).mpr rfl)
  have h2 := ht (c φ) (by rw [hdeg, hφ])
  rw [h1, hN, ← hq]
  exact h2

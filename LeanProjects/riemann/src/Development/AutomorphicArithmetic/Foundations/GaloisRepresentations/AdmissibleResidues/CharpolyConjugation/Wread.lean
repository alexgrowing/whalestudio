import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

theorem UpperTheory.GalN.V.L.wread :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (y : WD h), Continuous r → Unlinked r → (r '' (Ine (F := F) A : Set (G F Ω))).Finite → (∀ g : ↥(Weil h), (wdOf h hl ι r).charPol g = y.charPol g) → (y.mono0 → wdOf h hl ι r = y) → IsWDOf ι r y := by
  intro F Ω _ _ _ _ _ l _ n r ι w A h hl y hr hU hfin hpol hn
  obtain ⟨g, hg⟩ := UpperTheory.GalN.V.L.unlwd F Ω l ι n r w A h hl hr ((hU w hl A h hfin).unlAt)
  have hy : NoRatio y g := by
    simpa only [NoRatio, WD.eig, hpol] using hg
  rw [← hn (monodromyFree_of_noRatio hy)]
  exact isWDOf_wdOf hl ι (Units.continuous_val.comp hr)

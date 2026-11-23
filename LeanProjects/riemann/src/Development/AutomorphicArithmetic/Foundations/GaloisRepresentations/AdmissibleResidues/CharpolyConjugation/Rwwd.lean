import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RW

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Sd UpperTheory.GalN.V

theorem UpperTheory.GalN.V.L.rwwd :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), RatioW (wdOf h hl ι r)) → RW ι r := by
  intro F Ω _ _ _ _ _ l _ ι n r hr hW w hl A h s hs α β hα hβ
  have hc : Continuous fun g => ((r g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hact : WeilDeligne.ActsAs A (normV w) s 1 0 := by
    refine ⟨hs.1, fun x hx => ?_⟩
    simpa using hs.2 x hx
  let σ : Weil h := ⟨s, ⟨1, 0, hact⟩⟩
  have hdeg : deg σ = 1 := by
    rw [deg_eq (σ := σ) hact]
    norm_num
  have hmem : ∀ γ : Qbar l, (Matrix.charpoly ((r s : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).IsRoot γ →
      ι γ ∈ (wdOf h hl ι r).eig σ := by
    intro γ hγ
    show ι γ ∈ ((wdOf h hl ι r).charPol σ).roots
    rw [charPol_wdOf hl ι hc σ, Polynomial.mem_roots']
    exact ⟨((Matrix.charpoly_monic _).map _).ne_zero, hγ.map⟩
  exact hW w hl A h σ hdeg (ι α) (hmem α hα) (ι β) (hmem β hβ)

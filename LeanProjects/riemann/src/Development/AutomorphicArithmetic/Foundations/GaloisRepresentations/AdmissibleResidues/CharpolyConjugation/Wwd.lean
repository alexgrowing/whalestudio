import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

theorem UpperTheory.GalN.V.L.wwd :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal), Continuous r → (∀ g : ↥(Weil h), deg g = 1 → ∀ α ∈ (wdOf h hl ι r).eig g, ∀ β ∈ (wdOf h hl ι r).eig g, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖) → UnlinkAt r w A := by
  intro F Ω _ _ _ _ _ l _ n r ι w A h hl hr hlt
  have hc : Continuous fun g => (r g : Matrix (Fin n) (Fin n) (Qbar l)) :=
    Units.continuous_val.comp hr
  have hd : deg (frob h) = 1 := deg_frob (h := h)
  have hF := deg_eq_one_iff.1 hd
  have mem : ∀ x : Qbar l, ((r (frob h : Weil h).1 : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot x →
      ι x ∈ (wdOf h hl ι r).eig (frob h) := by
    intro x hx
    rw [WD.eig, charPol_wdOf hl ι hc]
    rw [Polynomial.mem_roots ((Matrix.charpoly_monic _).map _).ne_zero]
    exact (Polynomial.isRoot_map_iff (f := ι.toRingHom) ι.injective).2 hx
  refine ⟨(frob h : Weil h).1, 1, le_rfl, by simpa using hF, ?_⟩
  intro α β hα hβ k hk e
  have hlt' := hlt (frob h) hd _ (mem α hα) _ (mem β hβ)
  have e' : ‖ι α‖ ^ k = (((normV w ^ 1 : ℕ) : ℝ) * ‖ι β‖) ^ k := by
    have := congrArg (fun z => ‖ι z‖) e
    simpa [norm_pow, norm_mul, map_pow, map_mul] using this
  have e2 : ‖ι α‖ = ((normV w : ℕ) : ℝ) * ‖ι β‖ := by
    have := (pow_left_inj₀ (norm_nonneg _) (by positivity) (by omega)).1 e'
    simpa using this
  exact absurd hlt' (by rw [e2]; exact lt_irrefl _)

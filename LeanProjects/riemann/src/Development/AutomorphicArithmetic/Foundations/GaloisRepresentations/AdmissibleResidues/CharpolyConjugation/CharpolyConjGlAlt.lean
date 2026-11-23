import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem charpoly_conj_gl {k : Type} [Field k] {n : ℕ} (g a : GL (Fin n) k) :
    ((g * a * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly =
      (a : Matrix (Fin n) (Fin n) k).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem UpperTheory.GalN.V.L.wiso :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → Unlinked r → Unlinked r' := by
  intro F Ω _ _ _ _ _ l _ n r r' hiso hU w hw A hA hfin
  obtain ⟨g, hg⟩ := hiso
  have hfin' : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (hfin.image (fun x => g⁻¹ * x * g)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨r' s, ⟨s, hs, rfl⟩, ?_⟩
    simp only [hg s]
    group
  obtain ⟨s, j, hj, hF, h⟩ := hU w hw A hA hfin'
  refine ⟨s, j, hj, hF, ?_⟩
  intro α β hα hβ k hk
  rw [hg s, charpoly_conj_gl] at hα hβ
  exact h α β hα hβ k hk

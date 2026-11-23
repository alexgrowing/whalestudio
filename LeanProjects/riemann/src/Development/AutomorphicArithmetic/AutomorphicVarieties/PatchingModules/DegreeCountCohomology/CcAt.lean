import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cc_at (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : InfinitePlace F) (hw : w.IsReal) : ∃ c : G F Ω, IsCCAt w c := by
  classical
  let φ : F →+* ℂ := w.embedding
  have hφ : ∀ x, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    exact RingHom.congr_fun h x
  letI : Algebra F ℂ := φ.toAlgebra
  let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  let κ : ℂ ≃ₐ[F] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => hφ x)
  refine ⟨κ.restrictNormal Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgEquiv.restrictNormal_commutes κ Ω x
  · have e : j.toRingHom.comp (algebraMap F Ω) = φ := by
      ext x
      exact j.commutes x
    rw [e]
    exact InfinitePlace.mk_embedding w

theorem UpperTheory.V.Pa.ccEx :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ w : InfinitePlace (Lp L), ∃ c : G (Lp L) Ω, IsCCAt w c) ∧ ∀ c : G (Lp L) Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → c * c = 1 ∧ c ∉ (resP L Ω).range ∧ cycZ (Lp L) Ω l c = -1 := by
  intro l _ L Ω _ _ _ _ _ _
  haveI : Algebra.IsAlgebraic (Lp L) L := Algebra.IsAlgebraic.of_finite (Lp L) L
  haveI : IsAlgClosure (Lp L) Ω := IsAlgClosure.ofAlgebraic (Lp L) L Ω
  refine ⟨fun w => cc_at (Lp L) Ω w (IsTotallyReal.isReal w), ?_⟩
  rintro c ⟨j, hj⟩
  refine ⟨?_, ?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    apply j.injective
    show j (c (c x)) = j x
    rw [hj, hj, Complex.conj_conj]
  · rintro ⟨σ, hσ⟩
    have hfix : ∀ y : L, c (algebraMap L Ω y) = algebraMap L Ω y := by
      intro y
      rw [← hσ]
      exact σ.commutes y
    let ψ : L →+* ℂ := j.comp (algebraMap L Ω)
    have hreal : ComplexEmbedding.IsReal ψ := by
      rw [ComplexEmbedding.isReal_iff]
      ext y
      show starRingEnd ℂ (j (algebraMap L Ω y)) = j (algebraMap L Ω y)
      rw [← hj, hfix]
    have hR : (InfinitePlace.mk ψ).IsReal := InfinitePlace.isReal_mk_iff.mpr hreal
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) hR
  · exact UpperTheory.V.IsConjOm.cyc (E := L) (σ := MulSemiringAction.toRingAut (G (Lp L) Ω) Ω c) ⟨j, hj⟩

import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem pushCh_comp_alg {H O A B C : Type} [Group H] [CommRing O] [CommRing A] [CommRing B] [CommRing C]
    [Algebra O A] [Algebra O B] [Algebra O C] (f : A →ₐ[O] B) (g : B →ₐ[O] C) (χ : H →* Aˣ) :
    W.pushCh ((g.comp f : A →ₐ[O] C) : A →+* C) χ = W.pushCh (g : B →+* C) (W.pushCh (f : A →+* B) χ) := by
  ext s
  rfl

private theorem pushCh_id_alg {H O A : Type} [Group H] [CommRing O] [CommRing A] [Algebra O A] (χ : H →* Aˣ) :
    W.pushCh ((AlgHom.id O A : A →ₐ[O] A) : A →+* A) χ = χ := by
  ext s
  rfl

theorem UpperTheory.V.Ws.Eb.lamIso :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ Λ' : W.LamObj r), Nonempty (Λ.Λ ≃ₐ[O] Λ'.Λ) := by
  intro l _ F O _ _ _ n r Λ Λ'
  obtain ⟨f, hf, -⟩ := Λ.univ Λ'.Λ Λ'.κ Λ'.inert
  obtain ⟨g, hg, -⟩ := Λ'.univ Λ.Λ Λ.κ Λ.inert
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · exact (Λ'.univ Λ'.Λ Λ'.κ Λ'.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hg, hf]) (fun v i => pushCh_id_alg _)
  · exact (Λ.univ Λ.Λ Λ.κ Λ.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hf, hg]) (fun v i => pushCh_id_alg _)

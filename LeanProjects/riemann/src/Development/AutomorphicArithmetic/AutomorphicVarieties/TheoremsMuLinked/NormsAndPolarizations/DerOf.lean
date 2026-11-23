import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.derOf :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) [IsCO O (DualNumber O)] (p : Pair r (DualNumber O)) (D : GDet n O F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Oˣ), p.Maps (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) D ψ → ∃ (x : B.B →ₐ[O] O) (δ : B.B →ₗ[O] O), IsDer x δ ∧ B.u.Maps x.toRingHom D ψ ∧ (∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = (p.D.tr (MonoidAlgebra.single g 1)).snd) ∧ ∀ v i g, δ (B.u.ψ v i g : B.Bˣ) = ((p.ψ v i g : (DualNumber O)ˣ) : DualNumber O).snd := by
  intro l _ n F O _ _ _ r B _ p D ψ hp
  obtain ⟨f, ⟨hD, hψ⟩, -⟩ := B.univ (DualNumber O) p
  refine ⟨(TrivSqZeroExt.fstHom O O O).comp f, (TrivSqZeroExt.sndHom O O).comp f.toLinearMap, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    change (f (a * b)).snd = (f a).fst • (f b).snd + (f b).fst • (f a).snd
    rw [map_mul, DualNumber.snd_mul, smul_eq_mul, smul_eq_mul]
    ring
  · rw [← hp.1, ← hD, (UpperTheory.V.CA.d_gmap B.u.D).2.1]
    rfl
  · intro v i
    rw [← hp.2 v i, ← hψ v i]
    rfl
  · intro g
    have h := ((UpperTheory.V.CA.d_gmap B.u.D).2.2.1 (f : B.B →+* DualNumber O) (MonoidAlgebra.single g 1)).2 1
    rw [hD, MonoidAlgebra.mapRingHom_single, map_one] at h
    change (f (B.u.D.lam 1 (MonoidAlgebra.single g 1))).snd = (p.D.lam 1 (MonoidAlgebra.single g 1)).snd
    rw [h]
    rfl
  · intro v i g
    rw [← hψ v i]
    rfl

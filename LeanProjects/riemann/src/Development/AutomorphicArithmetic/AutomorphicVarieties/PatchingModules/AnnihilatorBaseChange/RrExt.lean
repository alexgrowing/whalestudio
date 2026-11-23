import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.TupMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrExt :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : W.R →ₐ[O] R'), (∀ i g, f (W.t.D.lam i (MonoidAlgebra.single g 1)) = f' (W.t.D.lam i (MonoidAlgebra.single g 1))) → (∀ v i g, f (W.t.ψ v i g) = f' (W.t.ψ v i g)) → f W.t.s = f' W.t.s → (∀ j i, f (W.t.U j i) = f' (W.t.U j i)) → (∀ j i, f (W.t.y j i) = f' (W.t.y j i)) → f = f' := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W R' _ _ _ f f' hD hψ hs hU hy
  obtain ⟨t', ht'⟩ := UpperTheory.V.Pa.Core.tupMap l L G0 T Λ n O r B u J D A W.R R' W.t f
  obtain ⟨-, -, hlam, -⟩ := UpperTheory.V.CA.d_gmap W.t.D
  have hl : ∀ (φ : W.R →+* R') i (g : Ph0 Λ), (W.t.D.map φ).lam i (MonoidAlgebra.single g 1) =
      φ (W.t.D.lam i (MonoidAlgebra.single g 1)) := fun φ i g => by
    have := (hlam φ (MonoidAlgebra.single g 1)).2 i
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  refine (W.univ R' t').unique ht' ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht'
  refine ⟨?_, fun v i => ?_, ?_, fun j i => ?_, fun j i => ?_⟩
  · rw [← h1]
    refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
    rw [hl, hl]
    exact (hD i g).symm
  · rw [← h2]
    ext g
    exact (hψ v i g).symm
  · exact hs.symm.trans h3
  · exact (hU j i).symm.trans (h4 j i)
  · exact (hy j i).symm.trans (h5 j i)

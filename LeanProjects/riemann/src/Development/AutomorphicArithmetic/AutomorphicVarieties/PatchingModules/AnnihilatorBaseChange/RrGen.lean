import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrExt
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrGen :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), GenBy O ({b | ∃ i g, b = W.t.D.lam i (MonoidAlgebra.single g 1)} ∪ {b | ∃ v i g, b = ((W.t.ψ v i g : W.Rˣ) : W.R)} ∪ {b | ∃ j i, b = W.t.U j i ∨ b = W.t.y j i} ∪ {W.t.s}) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W N x
  refine UpperTheory.V.CA.u_gen O W.R _ (fun R' _ _ _ f f' h => ?_) N x
  refine UpperTheory.V.Pa.Core.rrExt l L G0 T Λ n O r B u J D A W R' f f' (fun i g => h _ ?_) (fun v i g => h _ ?_)
    (h _ ?_) (fun j i => h _ ?_) (fun j i => h _ ?_)
  · exact .inl (.inl (.inl ⟨i, g, rfl⟩))
  · exact .inl (.inl (.inr ⟨v, i, g, rfl⟩))
  · exact .inr rfl
  · exact .inl (.inr ⟨j, i, .inl rfl⟩)
  · exact .inl (.inr ⟨j, i, .inr rfl⟩)

import Development.EtaleCohomology.TateTwists.HypercoverCechComparison

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts : Prop :=
  ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ),
    (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V),
    ∃ e : ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp ≅ (Arrow.mk (Ψ.map g).unop).cechNerve,
      lev Ψ (coAug g) = e.hom ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom

def LateralTheory.EtaleFoundations.CechQuasiIsoOfLocallySurjective : Prop :=
  ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (Arrow.mk f).augmentedCechNerve.hom)

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

def DensSymm : Prop :=
  ∀ (n : ℕ) (t : ℂ) (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)), dens t (z ∘ σ) = dens t z

def GammaEig : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
    ∫ x, (h : HeckeAlgebra μ) x * zonalSpherical μ z (g * x) ∂μ = evalAt z (satakeTransform μ h) * zonalSpherical μ z g

def InjAE : Prop := ∀ n : ℕ, ∀ᵐ θ : Fin n → UnitAddCircle, Function.Injective (pt θ)

end UpperTheory.Gal.Gen

end

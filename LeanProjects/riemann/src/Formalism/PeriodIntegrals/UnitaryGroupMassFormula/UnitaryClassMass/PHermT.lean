import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermCL

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def LocInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) (z : F) (c : 𝓞 F)
    (u : t.adicCompletion F), u ∈ t.adicCompletionIntegers F →
    algebraMap F (t.adicCompletion F) z = algebraMap F (t.adicCompletion F) (c : F) * u →
    ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F, z * (d : F) = (c : F) * (a : F)

def tcoord {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ TensorProduct.map (B.coord k) LinearMap.id

theorem tcoord_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] (x : E) (y : R) :
    tcoord B k R (x ⊗ₜ[F] y) = B.coord k x • y := by
  simp [tcoord]

end PI.UnitaryGroupMassFormula.UJClassMass

end

import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.PerfCard

namespace KStar.Selmer

open Matrix Module

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

def IsFrobeniusForm (θ : R →ₗ[S] S) : Prop :=
  Function.Bijective ((LinearMap.mul S R).compr₂ θ)

example : IsFrobeniusForm (LinearMap.id : S →ₗ[S] S) := by
  refine ⟨fun a b h => by simpa using LinearMap.congr_fun h 1, fun f => ⟨f 1, ?_⟩⟩
  ext
  simp

end KStar.Selmer

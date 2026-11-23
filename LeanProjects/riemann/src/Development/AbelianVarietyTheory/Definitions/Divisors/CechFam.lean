import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

def inter {ι : Type} (U : ι → X.Opens) (s : Finset ι) : X.Opens := s.inf U

def cechFam {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X)
    (a : ℕ) : Finset ι → AddSubgroup (abelian₂ X.functionField) :=
  fun s => logSec (suppAll E) G a (inter 𝒜.U s)

def Decomp (p : ℕ) {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι]
    (𝒜 : SncAtlas E n ι) : Prop :=
  ∀ (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ a b : ℕ,
    DI.HypZero (extD X.functionField) (fun q => cechFam 𝒜 (p • G + ∑ c, r c • E c) q) (a + b) →
      DI.CechZero (cechFam 𝒜 G a) b

end GlobalTheory.LogDR

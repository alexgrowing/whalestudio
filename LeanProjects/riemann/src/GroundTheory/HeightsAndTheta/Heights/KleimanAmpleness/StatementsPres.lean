import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def GradedPres.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type (max u v))
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module (Poly S N) F) (_ : Module S F)
      (_ : IsScalarTower S (Poly S N) F) (K : Type (max u v)) (_ : AddCommGroup K)
      (_ : Module (Poly S N) K) (_ : Module S K) (_ : IsScalarTower S (Poly S N) K)
      (𝓕 : GradedPMod S N F) (𝓚 : GradedPMod S N K) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) F)
      (d : Fin r → ℤ) (f : GradedHom 𝓚 𝓕) (g : GradedHom 𝓕 𝓜),
      (∀ j, b j ∈ 𝓕.piece (d j)) ∧ Module.Finite (Poly S N) K ∧ Function.Injective f.toLin ∧
        Function.Surjective g.toLin ∧ Function.Exact f.toLin g.toLin

def GradedULift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M),
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module (Poly S N) M') (_ : Module S M')
      (_ : IsScalarTower S (Poly S N) M') (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜')
      (g : GradedHom 𝓜' 𝓜), Function.LeftInverse g.toLin f.toLin ∧ Function.RightInverse g.toLin f.toLin

def CohomRetract.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v) (M' : Type w)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜),
    Function.LeftInverse g.toLin f.toLin → ∀ (i : ℕ) (c : ℤ), Function.Injective (cohomMap f i c)

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman

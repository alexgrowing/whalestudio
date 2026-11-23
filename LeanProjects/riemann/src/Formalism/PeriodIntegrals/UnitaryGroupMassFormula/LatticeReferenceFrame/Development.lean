import Mathlib
import Formalism.PeriodIntegrals.ScRefExists

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def GE (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.E) : Prop := ∃ t : 𝓞 I.E, x = (g : I.E) * (t : I.E)

def hG (I : Formalism.MainNotions.S.AutInst) (x y : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J x y

def SplitG (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
    Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2

def IsTheta (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (θ : 𝓞 I.E) : Prop :=
  GE I g ((θ : I.E) * θ - θ) ∧ GE I g ((θ : I.E) * star (θ : I.E)) ∧
    GE I g (1 - (θ : I.E) - star (θ : I.E))

def ThetaEx : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g → SplitG I g → ∃ θ : 𝓞 I.E, IsTheta I g θ

def IdemLift : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (θ : 𝓞 I.E), 1 ≤ g → SplitG I g → IsTheta I g θ →
    ∃ ε : I.E ⊗[I.F] Af I.F, ε ∈ IntAf I.F I.E ∧ ε * ε = ε ∧ ε * sigA I ε = 0 ∧
      ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) (θ : I.E))

def LocGlob : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (t : I.E), Formalism.UG.inclE (F := I.F) (Af I.F) t ∈ IntAf I.F I.E →
    ∃ s : 𝓞 I.E, (s : I.E) = t

def gL (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) {y | ∃ x ∈ I.L, y = (g : I.E) • x}

def GlobW : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    1 ≤ g → SplitG I g → IsTheta I g θ → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M g → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ (z : Fin I.n → I.E) (b bd : Fin k → Fin I.n → I.E),
      z ∈ I.L ∧ (∀ i, b i ∈ I.L ∧ bd i ∈ I.L) ∧
      (∀ a, hG I (e a) z = 0 ∧ hG I (f a) z = 0) ∧
      (∀ a i, hG I (e a) (b i) = 0 ∧ hG I (f a) (b i) = 0 ∧
        hG I (e a) (bd i) = 0 ∧ hG I (f a) (bd i) = 0) ∧
      GE I g (hG I z z + 1) ∧
      (∀ i, GE I g ((θ : I.E) * hG I z (b i)) ∧ GE I g (star (θ : I.E) * hG I z (bd i))) ∧
      (∀ i j, GE I g ((θ : I.E) * (hG I (bd i) (b j) - if i = j then 1 else 0))) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E)
        (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
          Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ⊔ gL I g

def Glue : Prop := ThetaEx → IdemLift → LocGlob → GlobW → PI.ScRefExists.Target

theorem target_of_steps (h0 : Glue) (h1 : ThetaEx) (h2 : IdemLift) (h3 : LocGlob) (h4 : GlobW) :
    PI.ScRefExists.Target := h0 h1 h2 h3 h4

end PI.ScRefExists.Sk

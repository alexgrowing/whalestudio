import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def smZ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (r : ℕ) (s : G ℚ Ω) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  Z r s y - (d₀ : Qbar l) * Z r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀))

def SmSys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl)
    (A : ValuationSubring Ω) (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), (d₀ : ZMod l) = 1 → (∀ x, ‖ψ x‖ ≤ 1) → Sys W c y S' → IwSys2 c A ν Z →
    SpLink A e (chiK l ψ) Z y →
    Sys W c (fun s => (1 - (d₀ : Qbar l) ^ (e + 1)) • y s) S' ∧ IwSys2 c A ν (smZ d₀ hd₀ Z) ∧
      SpLink A e (chiK l ψ) (smZ d₀ hd₀ Z) fun s => (1 - (d₀ : Qbar l) ^ (e + 1)) • y s

def ChiFix : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (χ : DirichletCharacter ℂ N) (χd : ℕ → ℤ_[l]),
    (∀ d : ℕ, d.Coprime N → ι (algebraMap ℚ_[l] (Qbar l) (χd d : ℚ_[l])) = χ d) →
    ∃ χ' : ℕ → ℤ_[l], (∀ d : ℕ, d.Coprime N → χ' d = χd d) ∧ (∀ d : ℕ, Nat.Coprime d N → IsUnit (χ' d)) ∧
      (∀ a b : ℕ, χ' (a * b) = χ' a * χ' b) ∧ ∀ a b : ℕ, a % N = b % N → χ' a = χ' b

end UpperTheory.V.Z.Kato.Joint

end

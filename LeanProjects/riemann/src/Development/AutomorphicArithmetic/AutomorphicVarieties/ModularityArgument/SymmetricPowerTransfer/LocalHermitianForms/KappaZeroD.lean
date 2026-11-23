import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra Glob

section

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

abbrev dS (j : (Etau K τ)ˣ →* DX Δ) (γ : DX Δ) : ℂ :=
  orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fun g => one (g ∈ KD Δ O)) γ

abbrev dK (j : (Etau K τ)ˣ →* DX Δ) (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ) : ℂ :=
  orb j (Cint O τ) (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fZD O χ) (j z)

end

def DIso : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∃ φ : DX Δ ≃* GL (Fin 2) K, (∀ g, φ g ∈ KG O K ↔ g ∈ KD Δ O) ∧
    (∀ z g, IsScal z g ↔ φ g = Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∧
    (∀ g, algebraMap K (Lsq K Δ) (φ g : Matrix (Fin 2) (Fin 2) K).det = (mt g).det) ∧
    ∀ (τ : K) (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
      ∃ j' : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K, j' ω = (φ γ : Matrix (Fin 2) (Fin 2) K) ∧ (j' ω).trace = τ ∧ ∀ z, φ (j z) = jU j' z

def DOrb : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    ∃ j' : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K, (j' ω).trace = τ ∧
      (∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → dS O j γ = gOrb O j' 1 a) ∧ ∀ χ : Kˣ →* ℂˣ, Unr O χ → ∀ z, dK O j χ z = gOrb O j' χ z

def StableD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → EvenVal O (c * (2 - τ)) → stabSum O c d m = dS O j γ

def KappaD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    ∀ c : K, EvenVal O (c * (2 - τ)) → ∀ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ → 2 + τ + QuadraticAlgebra.trace lam ≠ 0 →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ χ : Kˣ →* ℂˣ, IsChi O Δ χ →
    kapSum O c (dLam lam z) 1 =
      hs (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) * hs Δ (2 + τ + QuadraticAlgebra.trace lam) * hs (τ ^ 2 - 4) (-c) * dK O j χ z

def KappaZeroD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    (¬ ∃ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ) → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ χ : Kˣ →* ℂˣ, Unr O χ → dK O j χ z = 0

def VanishD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    τ ∉ (algebraMap O K).range → dS O j γ = 0 ∧ ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ χ : Kˣ →* ℂˣ, Unr O χ → dK O j χ z = 0

def FinD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    FinOrb j (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fun g => one (g ∈ KD Δ O)) γ ∧
    (∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ χ : Kˣ →* ℂˣ, FinOrb j (MonoidHom.id _) (ZD Δ ⊔ KD Δ O) (fZD O χ) (j z)) ∧
    ∀ y : DX Δ ⧸ (ZD Δ ⊔ KD Δ O), (MulAction.stabilizer (DX Δ) y).comap j ≤ Cint O τ ∧
      ((MulAction.stabilizer (DX Δ) y).comap j).relIndex (Cint O τ) ≠ 0

def OneD : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (γ : DX Δ) (j : (Etau K τ)ˣ →* DX Δ), HasTr γ τ → IsEmb τ γ j →
    γ ∈ KD Δ O → (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → (ZD Δ ⊔ KD Δ O).comap j = Cint O τ ∧
    (∀ y, y⁻¹ * γ * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u) ∧
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → j z ∈ KD Δ O ∧ ∀ y, y⁻¹ * j z * y ∈ ZD Δ ⊔ KD Δ O → ∃ t, ∃ u ∈ ZD Δ ⊔ KD Δ O, y = j t * u

def FzdLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ χ : Kˣ →* ℂˣ, Unr O χ → (∀ g : DX Δ, g ∉ ZD Δ ⊔ KD Δ O → fZD O χ g = 0) ∧
    ∀ (z : Kˣ) (s k : DX Δ), IsScal z s → k ∈ KD Δ O → fZD O χ (s * k) = (((χ z)⁻¹ : ℂˣ) : ℂ)

def FinUq : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    orb ι (Cint O τ) (theta Δ) (KU O Δ) (fun g => one (g ∈ KU O Δ)) δ = lcount O c d m ∧
    FinOrb ι (theta Δ) (KU O Δ) (fun g => one (g ∈ KU O Δ)) δ ∧
    ∀ y : U3 Δ ⧸ KU O Δ, (MulAction.stabilizer (U3 Δ) y).comap ι ≤ Cint O τ ∧ ((MulAction.stabilizer (U3 Δ) y).comap ι).relIndex (Cint O τ) ≠ 0

end UpperTheory.V.Z.Sym.Loc

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra

def dLam {K : Type} [Field K] {Δ τ : K} (lam : Lsq K Δ) (z : (Etau K τ)ˣ) : EL Δ τ :=
  lam • ofE Δ (star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))

abbrev jU {K : Type} [Field K] {τ : K} (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) : (Etau K τ)ˣ →* GL (Fin 2) K :=
  Units.map (j : Etau K τ →* Matrix (Fin 2) (Fin 2) K)

def LcountNorm : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ t ∈ NE τ, lcount O c d ((t : K) • m) = lcount O c d m

def OrbEq : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    uOrb O ι δ = lcount O c d m

def Vanish : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → lcount O c d m ≠ 0 → τ ∈ (algebraMap O K).range ∧ EvenVal O (c * (2 - τ))

def GVanish : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ), ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) → gOrb O j χ z ≠ 0 → τ ∈ (algebraMap O K).range

def Stable : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → EvenVal O (c * (2 - τ)) → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ (χ : Kˣ →* ℂˣ), Unr O χ →
    ∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → stabSum O c d m = gOrb O j χ a

def Kappa : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ c : K, EvenVal O (c * (2 - τ)) →
    ∀ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ → 2 + τ + QuadraticAlgebra.trace lam ≠ 0 →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ), (j ω).trace = τ →
    (∀ (x : Kˣ) (x₀ : O), algebraMap O K x₀ = x → (χ x : ℂ) = hs Δ (x : K) / (Nat.card (O ⧸ Ideal.span {x₀}) : ℂ)) →
    kapSum O c (dLam lam z) 1 =
      hs (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) * hs Δ (2 + τ + QuadraticAlgebra.trace lam) * hs (τ ^ 2 - 4) (-c) * gOrb O j χ z

def KappaZero : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → (¬ ∃ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ) →
    kapSum O c d m = 0 ∧ ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ), (z : Etau K τ) = 1 + ω → gOrb O j χ z = 0

def DatLam : Prop :=
  ∀ (K : Type) [Field K] (Δ τ c : K), τ ^ 2 - 4 ≠ 0 → c ≠ 0 → ∀ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → IsDat c (dLam lam z) 1

def DatSmul : Prop :=
  ∀ (K : Type) [Field K] (Δ τ c : K) (d m : EL Δ τ), IsDat c d m → ∀ t : Kˣ, IsDat c d ((t : K) • m)

def LocNorm : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ∈ (algebraMap O K).range → ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau K τ)

def FinU : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    ∃ s : Finset (U3 Δ), ∀ y : U3 Δ, y⁻¹ * δ * theta Δ y ∈ KU O Δ → ∃ z, ∃ x ∈ s, ∃ k ∈ KU O Δ, y = ι z * x * k

def StabU : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    ∀ y : U3 Δ, ((KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom).comap ι ≤ Cint O τ ∧
      (((KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom).comap ι).relIndex (Cint O τ) ≠ 0

def OneU : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ (δ : U3 Δ) (ι : (Etau K τ)ˣ →* U3 Δ) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)), Models c d m δ ι P →
    δ ∈ KU O Δ → (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) →
    (∀ y : U3 Δ, y⁻¹ * δ * theta Δ y ∈ KU O Δ ↔ ∃ z, ∃ k ∈ KU O Δ, y = ι z * k) ∧ (KU O Δ).comap ι = Cint O τ

def FinG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ z : (Etau K τ)ˣ, (z : Etau K τ).im ≠ 0 →
    ∃ s : Finset (GL (Fin 2) K), ∀ y : GL (Fin 2) K, y⁻¹ * jU j z * y ∈ ZK O K → ∃ t, ∃ x ∈ s, ∃ k ∈ ZK O K, y = jU j t * x * k

def StabG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → ∀ y : GL (Fin 2) K,
    ((ZK O K).comap (MulAut.conj y⁻¹).toMonoidHom).comap (jU j) ≤ Cint O τ ∧
      (((ZK O K).comap (MulAut.conj y⁻¹).toMonoidHom).comap (jU j)).relIndex (Cint O τ) ≠ 0

def OneG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → (∀ s t, j ω s t ∈ (algebraMap O K).range) → (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) →
    (ZK O K).comap (jU j) = Cint O τ ∧ ∀ z : (Etau K τ)ˣ, ((z : Etau K τ) = ω ∨ (z : Etau K τ) = 1 + ω) →
      jU j z ∈ KG O K ∧ ∀ y : GL (Fin 2) K, y⁻¹ * jU j z * y ∈ ZK O K ↔ ∃ t, ∃ k ∈ ZK O K, y = jU j t * k

def FzkLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ χ : Kˣ →* ℂˣ, Unr O χ → (∀ g, g ∉ ZK O K → fZK O χ g = 0) ∧
    ∀ (z : Kˣ), ∀ k ∈ KG O K, fZK O χ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * k) = (((χ z)⁻¹ : ℂˣ) : ℂ)

def HsMul : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ D x y : K, D ≠ 0 → x ≠ 0 → y ≠ 0 → hs D (x * y) = hs D x * hs D y

def HsLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    (∀ x y : K, x ≠ 0 → y ≠ 0 → hs x y = hs y x) ∧ (∀ x y : K, EvenVal O x → EvenVal O y → hs x y = 1) ∧
    (∀ D : K, D ≠ 0 → ¬ IsSquare D → ∃ x : K, x ≠ 0 ∧ hs D x = -1) ∧ ∀ D x : K, D ≠ 0 → IsSquare D → hs D x = 1

def HsNE : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ t : Kˣ, t ∈ NE τ ↔ hs (τ ^ 2 - 4) (t : K) = 1

def EtaEx : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∃ η : Kˣ →* ℂˣ, Unr O η ∧ ∀ x, (η x : ℂ) = hs Δ (x : K)

def SplitJ : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∃ P : GL (Fin 2) (Lsq K Δ), (∀ s t, IsInt O ((P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) s t) ∧ IsInt O (((P⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) s t)) ∧
      ∀ X : Matrix (Fin 2) (Fin 2) (Lsq K Δ), !![0, 1; -1, 0] * X.map star = X * !![0, 1; -1, 0] ↔
        ((P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))).map star = (P : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * X * (P⁻¹ : GL (Fin 2) (Lsq K Δ))

end UpperTheory.V.Z.Sym.Loc

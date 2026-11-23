import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

def LdShape (q : ℂ) (γ : RatFunc ℂ) (k : ℕ) : Prop :=
  ∃ (P : ℂ[X]) (c : ℂ) (j : ℤ), P.eval 0 = 1 ∧ P.natDegree = k ∧ c ≠ 0 ∧
    γ = RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C q * X))

def LdLaurent : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (m : ℕ) [NeZero m]
    [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (α : ℂ) (c : GL (Fin m) F → ℂ), IsCentralCoeff m α c →
    (∀ k : ℤ, ∫ g in {g : GL (Fin m) F | ordDet g = k}, c g ∂μ = 0) →
    ∀ Φ : Matrix (Fin m) (Fin m) F → ℂ, IsSchwartzBruhat Φ → ∃ (S : Finset ℤ) (a : ℤ → ℂ), ∀ s : ℂ,
      ‖α * qs F s ^ m‖ < 1 →
        ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * c g ∂μ = ∑ k ∈ S, a k * qs F s ^ k

def LdMean : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (m : ℕ) [NeZero m]
    [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] [SecondCountableTopology H] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin m) F × H) W),
    IsAdmissible σ → σ.IsIrreducible → ∀ α : ℂ, α ≠ 0 → (∀ v, σ (centralUnif F m, 1) v = α • v) →
    (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), ∃ C : Set (GL (Fin m) F), IsCompact C ∧
      ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C) →
    ¬ (m = 1 ∧ ∀ g ∈ integralGL F m, σ (g, 1) = 1) →
    ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), ∀ k : ℤ,
      ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) v) ∂μ = 0 ∧
      ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) v) ∂μ = 0

def LdTate : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace (GL (Fin 1) F)] [BorelSpace (GL (Fin 1) F)] (μ : Measure (GL (Fin 1) F)) [μ.IsHaarMeasure],
    ∃ Φ : Matrix (Fin 1) (Fin 1) F → ℂ, IsSchwartzBruhat Φ ∧ ∃ r : ℂ, r ≠ 0 ∧ ∀ (α : ℂ) (c : GL (Fin 1) F → ℂ),
      IsCentralCoeff 1 α c → (∀ g ∈ integralGL F 1, c g = c 1) → ∀ s : ℂ, ‖α * qs F s ^ 1‖ < 1 →
        ∫ g, Φ (g : Matrix (Fin 1) (Fin 1) F) * detPow g s * c g ∂μ = r * c 1 / (1 - α * qs F s)

def LdUnique : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (n : ℕ) (β : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W),
    IsAdmissible σ → σ.IsIrreducible → ∀ (κ : levi F n β →* ℝ≥0), Continuous κ →
    ∀ (μ : Measure (levi F n β)) [μ.IsHaarMeasure] (ψ : AddChar F Circle) (γ γ' : RatFunc ℂ),
    LeviFE F σ κ μ ψ γ → LeviFE F σ κ μ ψ γ' → γ = γ'

def LdBlock : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (m : ℕ) [NeZero m]
    [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] [SecondCountableTopology H] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin m) F × H) W),
    IsAdmissible σ → σ.IsIrreducible → ∀ α : ℂ, α ≠ 0 → (∀ v, σ (centralUnif F m, 1) v = α • v) →
    (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), ∃ C : Set (GL (Fin m) F), IsCompact C ∧
      ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C) →
    ∀ ψ : AddChar F Circle, Continuous ψ → ψ ≠ 1 → ∀ γ : RatFunc ℂ,
    (∀ Φ : Matrix (Fin m) (Fin m) F → ℂ, IsSchwartzBruhat Φ → ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      RatFE F γ (blockA μ σ Φ v ℓ) (blockB μ σ (GJMatrix.localMatrixFourier ψ Φ) v ℓ)) →
    LdShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ (if m = 1 ∧ ∀ g ∈ integralGL F m, σ (g, 1) = 1 then 1 else 0)

end UpperTheory.V.Z.Gam

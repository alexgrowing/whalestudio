import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

namespace PI.HodgeOfFon

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def FonDim : Prop :=
  ∀ T : LocLat G Qp LL O,
    (Module.Finite LL ↥(Dcris PD T.ρ) ∧
      finrank LL ↥(Dcris PD T.ρ) ≤ finrank Qp K₀ * finrank LL T.V) ∧
    ∀ τ : K →ₐ[Qp] LL, Module.Finite LL ↥(DdRE PD T.ρ τ) ∧
      finrank LL ↥(DdRE PD T.ρ τ) ≤ finrank LL T.V

def FonStrict : Prop :=
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₁.ρ →
    IsCrys PD T₀.ρ ∧ IsCrys PD T₂.ρ ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
        multV PD T₁.ρ τ a = multV PD T₀.ρ τ a + multV PD T₂.ρ τ a) ∧
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Function.Surjective F.f →
    IsCrys PD T₁.ρ →
    IsCrys PD T₂.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD T₂.ρ τ a ≤ multV PD T₁.ρ τ a

end Lit

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def CrysLat (T : LocLat G Qp LL O) : Prop :=
  FiniteDimensional LL T.V ∧ IsModuleTopology LL T.V ∧ (∀ x, Continuous fun g => T.ρ g x) ∧
    IsCrys PD T.ρ

variable (LL O) in

def HodgeExact : Prop :=
  (∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → CrysLat PD T₁ →
      CrysLat PD T₀ ∧ CrysLat PD T₂ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
        IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a) ∧
  (∀ T : LocLat G Qp LL O, (∀ g x, T.ρ g x = x) →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T.ρ τ a → a = 0)

end Local

end PI.HodgeOfFon

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module in

def PI.HodgeOfFon : Prop :=
  ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL],
    PI.HodgeOfFon.FonDim PD LL O → PI.HodgeOfFon.FonStrict PD LL O → PI.HodgeOfFon.HodgeExact PD LL O

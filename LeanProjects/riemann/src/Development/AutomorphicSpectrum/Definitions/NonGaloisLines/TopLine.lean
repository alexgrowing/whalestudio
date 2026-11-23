import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

def cupQ {LL O : Type} [Field LL] [CommRing O] [Algebra O LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (LA : Lattice (O := O) ρ)
    (LA' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O) (r : ℕ)
    (c : G → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (c' : G → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) (x : G × G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (LocalSituation.liftQ LA _ (c x.1)) (ρ' x.1 (LocalSituation.liftQ LA' _ (c' x.2)))

def FinZQ (_PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Finite ↥(quotientCocycles LA _ hI)

def TopInj : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (z : G × G → LL), (∀ x, algebraMap O LL ϖ ^ r * z x ∈ L1.T) →
    CobO PD L1 z → ∃ f : G → LL, (∀ g, algebraMap O LL ϖ ^ r * f g ∈ L1.T) ∧
      IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : LL ⧸ L1.T)) ∧
      ∀ x, ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x - z x ∈ L1.T

def DualQ : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ (A A' : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 PD LA LA' P →
  ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)),
    (∀ S, BQ LA _ hI ≤ S → S ≤ quotientCocycles LA _ hI → ∀ c ∈ quotientCocycles LA _ hI,
      (∀ c' ∈ quotientCocycles LA' _ hI', (∀ s ∈ S, CobO PD L1 (cupQ LA LA' P ϖ r s c')) →
        CobO PD L1 (cupQ LA LA' P ϖ r c c')) → c ∈ S) ∧
    (∀ S', BQ LA' _ hI' ≤ S' → S' ≤ quotientCocycles LA' _ hI' → ∀ c' ∈ quotientCocycles LA' _ hI',
      (∀ c ∈ quotientCocycles LA _ hI, (∀ s ∈ S', CobO PD L1 (cupQ LA LA' P ϖ r c s)) →
        CobO PD L1 (cupQ LA LA' P ϖ r c c')) → c' ∈ S')

def DualD : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ (A A' : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 PD LA LA' P →
  ∀ S, BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA',
    (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO PD L1 (cupLD LA' P d s)) → CobO PD L1 (cupLD LA' P d c)) → c ∈ S

def CobLO : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ z : G × G → LL, Continuous z → (CobL PD z ↔ ∀ a : LL, CobO PD L1 (a • z))

def TopLine : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ z z' : G × G → LL, Continuous z → Continuous z' →
    ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0 → ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z' = 0 →
    ¬ CobL PD z → ∃ a : LL, CobL PD (z' - a • z)

def NondegL : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P →
    (∀ a ∈ continuousCocycles A.ρ, (∀ b ∈ continuousCocycles A'.ρ, CobL PD (cupL A'.ρ P a b)) → a ∈ B1 A.ρ) ∧
    (∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL PD (cupL A'.ρ P a b)) → b ∈ B1 A'.ρ)

def EulerL : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P →
    Module.Finite LL (H1V A.ρ) ∧
    finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank Qp K * finrank LL A.V

def OrthL : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P → IsDR PD A.ρ →
    ∀ a ∈ finiteCocycles PD A.ρ, ∀ b ∈ finiteCocycles PD A'.ρ, CobL PD (cupL A'.ρ P a b)

def DualL : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P →
    (∀ (S : Submodule LL (G → A.V)) (S' : Submodule LL (G → A'.V)), B1 A.ρ ≤ S → S ≤ continuousCocycles A.ρ →
      B1 A'.ρ ≤ S' → S' ≤ continuousCocycles A'.ρ → (∀ a ∈ S, ∀ b ∈ S', CobL PD (cupL A'.ρ P a b)) →
      finrank LL (H1V A.ρ) ≤ finrank LL (↥S ⧸ (B1 A.ρ).comap S.subtype) +
        finrank LL (↥S' ⧸ (B1 A'.ρ).comap S'.subtype) →
      (∀ a ∈ continuousCocycles A.ρ, (∀ b ∈ S', CobL PD (cupL A'.ρ P a b)) → a ∈ S) ∧
      (∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ S, CobL PD (cupL A'.ρ P a b)) → b ∈ S'))

def All : Prop :=
  FinZQ PD ∧ TopInj PD ∧ DualQ PD ∧ DualD PD ∧ CobLO PD ∧ TopLine PD ∧ NondegL PD ∧ EulerL PD ∧ DualL PD

end GlobalTheory.CompanionTheory.LocDual

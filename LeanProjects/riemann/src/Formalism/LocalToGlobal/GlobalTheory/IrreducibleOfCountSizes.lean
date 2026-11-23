import Formalism.LocalToGlobal.GlobalTheory.FamColC
import Formalism.PadicSubsetSums.CentralIdempotents.StretchedExponentialDominance
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily

open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcN

open Formalism Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def IrrAt {C : ColObj K I} (R : RowArg C) (x ε : ℝ) : Prop :=
  (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

def ShareAt {C : ColObj K I} (R : RowArg C) (εC W₁ W₂ : ℝ) : Prop :=
  (Fintype.card R.κ₁ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (1 + εC) / (1 - εC) * (W₁ + W₂)

def CountAt {C : ColObj K I} (R : RowArg C) (εC W₁ W₂ : ℝ) : Prop :=
  ∃ PP₁ PP₂ D₁ D₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Fintype.card (R.κ ⊕ R.κ₁) : ℝ) - Dstar| ≤ εC * Dstar ∧
    |D₁ - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧ |D₂ - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar) ∧
    (Fintype.card R.κ₁ : ℝ) ≤ D₁ + D₂

end Defs

def NumbersAt (x ε εC C W₁ W₂ : ℝ) : Prop :=
  0 ≤ εC ∧ εC ≤ 1 / 2 ∧ W₁ ≤ x ^ C * Real.exp (-(x ^ (ε / 6))) ∧ W₂ ≤ x ^ C * Real.exp (-(x ^ (ε / 6)))

def IrreducibleOfShare : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
    (x ε εC W₁ W₂ : ℝ),
    ShareAt R εC W₁ W₂ → (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ LChain6.E7 x ε → IrrAt R x ε

def ShareFromCountRows : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount →
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
    (εC W₁ W₂ : ℝ), CountAt R εC W₁ W₂ → ShareAt R εC W₁ W₂

def NumbersDominantLarge : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop, ∀ εC W₁ W₂ : ℝ,
    NumbersAt x ε εC C W₁ W₂ → (1 + εC) / (1 - εC) * (W₁ + W₂) ≤ LChain6.E7 x ε

def IrreducibleOfCount : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ C0 ε : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
      (εC W₁ W₂ : ℝ), CountAt R εC W₁ W₂ → NumbersAt x ε εC C0 W₁ W₂ → IrrAt R x ε

def Wg (f m N g q₁ d : ℕ) : ℝ :=
  3 * (f : ℝ) / (g : ℝ) +
    23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) +
    2 * (f : ℝ) * (m : ℝ) * (1 / (4 * ((min q₁ d : ℕ) : ℝ)) + (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) +
    (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f +
    Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ)))

def epsC (c : ℝ) (N f : ℕ) : ℝ := Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ)))

def SizesAt (x ε Cs : ℝ) (f m N g q₁ d : ℕ) : Prop :=
  Real.exp (8 * x ^ ε) ≤ (g : ℝ) ∧ x ^ 2 ≤ (f : ℝ) ∧ (f : ℝ) ≤ x ^ Cs ∧ (m : ℝ) ≤ x ^ Cs ∧
    100 ≤ N ∧ (N : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (ε / 6)) ≤ ((min q₁ d : ℕ) : ℝ)

def WeightNumbersBound : Prop :=
  ∀ ε Cs : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℝ in Filter.atTop, ∀ f m N g q₁ d : ℕ,
    SizesAt x ε Cs f m N g q₁ d → Wg f m N g q₁ d ≤ x ^ (3 * Cs + 3) * Real.exp (-(x ^ (ε / 6)))

def EpsilonBoundLargeX : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in Filter.atTop, ∀ N f : ℕ, 100 ≤ N → x ^ 2 ≤ (f : ℝ) → epsC c N f ≤ 1 / 2

def IrreducibleOfCountSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ ε Cs c : ℝ, 0 < ε → ε ≤ 1 → 0 < c → ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
      (f m N g₁ g₂ q₁ d : ℕ), SizesAt x ε Cs f m N g₁ q₁ d → SizesAt x ε Cs f m N g₂ q₁ d →
      CountAt R (epsC c N f) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) → IrrAt R x ε

def CountBoundForCompatibleRows {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {C : ColObj K I} (R : RowArg C)
    {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = Fintype.card (R.κ ⊕ R.κ₁) ∧
  Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = Fintype.card R.κ₁ ∧
  ∃ PP₁ PP₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar)

def CompatibleCountArithmetic : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion →
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
    (k : Type) [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ), CountBoundForCompatibleRows R HH e₁ e₂ εC W₁ W₂ → CountAt R εC W₁ W₂

def IrreducibleOfCompatibleSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ ε Cs c : ℝ, 0 < ε → ε ≤ 1 → 0 < c → ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) (C : ColObj K I) (R : RowArg C)
      (k : Type) [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
      (e₁ e₂ : HH →ₗ[k] HH) (f m N g₁ g₂ q₁ d : ℕ),
      SizesAt x ε Cs f m N g₁ q₁ d → SizesAt x ε Cs f m N g₂ q₁ d →
      CountBoundForCompatibleRows R HH e₁ e₂ (epsC c N f) (Wg f m N g₁ q₁ d) (Wg f m N g₂ q₁ d) → IrrAt R x ε

section Rec

open Formalism.BasicNotions Formalism.MainNotions

def CountBoundForCompatibleRowsRecursive (D : D7) {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH]
    [FiniteDimensional k HH] (e₁ e₂ : HH →ₗ[k] HH) (εC W₁ W₂ : ℝ) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = D.what₂.Dall ∧
  D.what₂.Drows + Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = D.what₂.Dall ∧
  ∃ PP₁ PP₂ Dstar : ℝ, 0 ≤ εC ∧ εC < 1 ∧ 0 < Dstar ∧
    0 ≤ PP₁ ∧ PP₁ ≤ W₁ ∧ 0 ≤ PP₂ ∧ PP₂ ≤ W₂ ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP₁ * Dstar| ≤ εC * (PP₁ * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP₂ * Dstar| ≤ εC * (PP₂ * Dstar)

def SizesRec (D : D7) (x ε Cs : ℝ) : Prop :=
  ∀ j : Fin 2, SizesAt x ε Cs D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

def IrreducibleOfCompatibleForms : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
    (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
    [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SizesRec (Fm.D x i) x Fm.ez Cs ∧
      CountBoundForCompatibleRowsRecursive (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f)
        (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 0) (Fm.D x i).host.q (Fm.D x i).host.d)
        (Wg (Fm.D x i).R.f (Fm.D x i).R.m (Fm.D x i).R.r ((Fm.D x i).host.g 1) (Fm.D x i).host.q (Fm.D x i).host.d)) →
    LinkIRR Fm

end Rec

section Inputs

open Formalism.BasicNotions Formalism.MainNotions

def AllRowsRec (D : D7) {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH]
    [FiniteDimensional k HH] (e₁ e₂ : HH →ₗ[k] HH) : Prop :=
  e₁ ∘ₗ e₁ = e₁ ∧ e₂ ∘ₗ e₂ = e₂ ∧ e₁ ∘ₗ e₂ = e₂ ∘ₗ e₁ ∧
  Module.finrank k HH = D.what₂.Dall ∧
  D.what₂.Drows + Module.finrank k (LinearMap.range (e₁ + e₂ - e₁ ∘ₗ e₂)) = D.what₂.Dall

def CountRec {k : Type} [Field k] (HH : Type) [AddCommGroup HH] [Module k HH] [FiniteDimensional k HH]
    (e₁ e₂ : HH →ₗ[k] HH) (εC : ℝ) (PP : Fin 2 → ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ ∃ Dstar : ℝ, 0 < Dstar ∧
    |(Module.finrank k HH : ℝ) - Dstar| ≤ εC * Dstar ∧
    |(Module.finrank k (LinearMap.range e₁) : ℝ) - PP 0 * Dstar| ≤ εC * (PP 0 * Dstar) ∧
    |(Module.finrank k (LinearMap.range e₂) : ℝ) - PP 1 * Dstar| ≤ εC * (PP 1 * Dstar)

def WeightRec (D : D7) (PP : Fin 2 → ℝ) : Prop :=
  ∀ j : Fin 2, 0 ≤ PP j ∧ PP j ≤ Wg D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

def LinkIrreducibleInputs : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BadRankUnion → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps) (k : Type) [Field k]
    (HH : ∀ x, Fm.Ix x → Type) [∀ x i, AddCommGroup (HH x i)] [∀ x i, Module k (HH x i)]
    [∀ x i, FiniteDimensional k (HH x i)] (e₁ e₂ : ∀ x i, HH x i →ₗ[k] HH x i) (PP : ∀ x, Fm.Ix x → Fin 2 → ℝ),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      AllRowsRec (Fm.D x i) (HH x i) (e₁ x i) (e₂ x i) ∧
      CountRec (HH x i) (e₁ x i) (e₂ x i) (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) (PP x i) ∧
      WeightRec (Fm.D x i) (PP x i) ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) →
    LinkIRR Fm

end Inputs

section AllRowsIn

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

def DstarE {D : D7} (A : AllRows D) (e : A.B.I.Gf → ℂ) : ℝ :=
  A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund e

def CountAllRows {D : D7} (A : AllRows D) (εC : ℝ) : Prop :=
  0 ≤ εC ∧ εC < 1 ∧ 0 < DstarE A A.B.e ∧
    ∀ (k : Fin 2) (S : Set (Tup D k)),
      |(A.dimT (cyl D k S) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤ εC * DstarE A (A.eT (cyl D k S))

def WeightAllRows {D : D7} (A : AllRows D) : Prop :=
  (∀ (k : Fin 2) v f, 0 ≤ wtOf D k (A.eVec k v) f) ∧
    ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
      locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d

def FamilyIrreducibleOfCountWeightSizes : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.ShareFromCount → Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.StretchedExponentialDominance →
  ∀ (eps Cs c : ℝ), 0 < eps → eps ≤ 1 → 0 < c → ∀ (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧
      CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧
      WeightAllRows A ∧
      SizesRec (Fm.D x i) x Fm.ez Cs) →
    LinkIRR Fm

end AllRowsIn

end Formalism.L2.GlobalTheoryTheory.ConcN

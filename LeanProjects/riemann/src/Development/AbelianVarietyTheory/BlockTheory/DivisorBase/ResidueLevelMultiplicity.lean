import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueLevelMultiplicity

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

variable {E : Type} [Field E] [NumberField E]

abbrev resField (PP : Pl E) : Field (kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

theorem finite_res (PP : Pl E) : Finite (kP PP) :=
  Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

theorem finite_boundedLevelClassGroupFamily (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  haveI := fun PP : Pl E => finite_res PP
  infer_instance

def IsParCuspChar (F : Type) [Field F] (r : ℕ) (θ : GL (Fin r) F → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (d : ℕ) (σ : Representation ℂ (blockTri (κ := F) b) (Fin d → ℂ)),
    IsCuspDatum b σ ∧ ∀ g, θ g = LinearMap.trace ℂ _ (parInd b σ g)

def IsProdParCusp {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsParCuspChar (kP PP.1) (resField PP.1) r (θ PP)) ∧
      ∀ g : G0 Pg r, s (χ g) = ∏ PP : ↥Pg, θ PP (g PP)

def lvlMult {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  haveI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ * ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def nbar (Pg : Finset (Pl E)) (k : ℕ) : ℕ := ∏ PP ∈ Pg, Nat.card (kP PP) ^ k

def MultNear {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K)
    (N : ℕ) (δ : ℝ) : Prop :=
  ∃ n : ℕ, lvlMult P χ = (n : K) ∧ |(n : ℝ) - (N : ℝ)| ≤ δ * (N : ℝ)

def MultPsharp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (f g r ρ k : ℕ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    1 ≤ k → r = k + 2 * ρ + 1 → Pg.card = 2 * f → 0 < g → 4 * f * r ≤ g →
    (∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) → IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsProdParCusp s Pg r χ →
      MultNear (PsharpSym Pg r ρ k ψ) χ (nbar Pg k) (8 * (f : ℝ) * r / g) ∧
      MultNear (Psharp Pg r k ψ) χ (nbar Pg k) (8 * (f : ℝ) * r / g)

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueLevelMultiplicity

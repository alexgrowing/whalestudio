import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

def IsCuspIndChar {F : Type} [Field F] {r : ℕ} (θ : GL (Fin r) F → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (σ : Representation ℂ (blockTri (κ := F) b) V),
    IsCuspDatum b σ ∧ ∀ g : GL (Fin r) F, θ g = LinearMap.trace ℂ _ (parInd b σ g)

abbrev kField {E : Type} [Field E] [NumberField E] (PP : Pl E) : Field (kP PP) :=
  Ideal.Quotient.field PP.asIdeal

def IsCuspIndProdChar {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsCuspIndChar (kP PP.1) (kField PP.1) r (θ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) = ∏ PP : ↥Pg, θ PP (g PP)

theorem finite_boundedLevelClassGroupFamily {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  haveI : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : ∀ PP : ↥Pg, Finite (GL (Fin r) (kP PP.1)) := fun PP => inferInstance
  exact Pi.finite

abbrev fintypeH {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [CommRing K]
    (P : LevelP Pg r K) : Fintype P.H :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  Fintype.ofFinite _

def lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  letI := fintypeH P
  ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def OneWhittakerVector : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsCuspIndProdChar Pg r s χ →
      lvlSum (P0 Pg r ψ) χ = (Nat.card (P0 Pg r ψ).H : K)

def OneWhittakerVectorDim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) [Fintype (G0 Pg r)]
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    IsGenericPsi Pg ψ →
    ∀ (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K (G0 Pg r)) (t : T.S),
      IsCuspIndProdChar Pg r s (fun g => LinearMap.trace K (T.W t) (T.tau t g)) →
      Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨(P0 Pg r ψ).H, (P0 Pg r ψ).chi⟩ t = 1

example {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (h : ∀ x : P.H, χ x = (P.chi x : K)) :
    lvlSum P χ = (Nat.card P.H : K) := by
  unfold lvlSum
  letI := fintypeH P
  simp [h, Nat.card_eq_fintype_card]

example {E : Type} [Field E] [NumberField E] (r : ℕ) {K : Type} [Field K] (s : K →+* ℂ) :
    IsCuspIndProdChar (∅ : Finset (Pl E)) r s (fun _ => 1) :=
  ⟨fun _ _ => 1, fun PP => absurd PP.2 (Finset.notMem_empty _), fun g => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter

import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

open Formalism.L2.DIV NumberField

variable {E : Type} [Field E] [NumberField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_kP (PP : _root_.Formalism.L2.DIV.Pl E) : Finite (_root_.Formalism.L2.DIV.kP PP) := by
  unfold _root_.Formalism.L2.DIV.kP
  exact Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

open NumberField in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_boundedLevelClassGroupFamily (Pg : Finset (_root_.Formalism.L2.DIV.Pl E)) (r : ℕ) :
    Finite (_root_.Formalism.L2.DIV.G0 Pg r) := by
  haveI : ∀ PP : ↥Pg, Finite (_root_.Formalism.L2.DIV.kP PP.1) := fun PP =>
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_kP PP.1
  unfold _root_.Formalism.L2.DIV.G0
  infer_instance

def IsCuspProdChar {κ : Type} [Field κ] {r : ℕ} (θ : GL (Fin r) κ → ℂ) : Prop :=
  ∃ (d : ℕ) (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := κ) b) (Fin d → ℂ)),
    FinGL.IsCuspDatum b σ ∧ ∀ x, θ x = (FinGL.parInd b σ).character x

def IsProdCuspChar {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) r (θ PP)) ∧
      ∀ x : G0 Pg r, s (χ x) = ∏ PP : ↥Pg, θ PP (x PP)

def levelMult {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  haveI : Fintype P.H := Fintype.ofFinite _
  (Nat.card P.H : K)⁻¹ * ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def nbar (Pg : Finset (Pl E)) (k : ℕ) : ℕ := ∏ PP ∈ Pg, Nat.card (kP PP) ^ k

def MultNear {K : Type} [Field K] {Pg : Finset (Pl E)} {r : ℕ} (P : LevelP Pg r K) (χ : G0 Pg r → K) (N δ : ℝ) : Prop :=
  ∃ n : ℕ, levelMult P χ = (n : K) ∧ |(n : ℝ) - N| ≤ δ * N

def MultSharp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (f g r ρ k : ℕ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    Pg.card = 2 * f → 1 ≤ k → r = k + 2 * ρ + 1 → 0 < g → 4 * f * r ≤ g →
    (∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) → IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsProdCuspChar s Pg r χ →
      MultNear (PsharpSym Pg r ρ k ψ) χ (nbar Pg k) (8 * f * r / g) ∧
        MultNear (Psharp Pg r k ψ) χ (nbar Pg k) (8 * f * r / g)

example {κ : Type} [Field κ] [Finite κ] {r d : ℕ} (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := κ) b) (Fin d → ℂ)) :
    Module.Finite ℂ (Representation.coindV (blockTri (κ := κ) b).subtype σ) := inferInstance

open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar_pos (Pg : Finset (_root_.Formalism.L2.DIV.Pl E)) (k : ℕ) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar Pg k := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar
  refine Finset.prod_pos fun PP _ => pow_pos ?_ k
  haveI := _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_kP PP
  haveI : Nonempty (_root_.Formalism.L2.DIV.kP PP) := ⟨0⟩
  exact Nat.card_pos

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

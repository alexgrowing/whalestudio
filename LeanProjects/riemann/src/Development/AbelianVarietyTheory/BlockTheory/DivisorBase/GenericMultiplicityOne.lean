import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

variable {E : Type} [Field E] [NumberField E]

@[reducible] def resField (PP : Pl E) : Field (kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

attribute [local instance] resField

theorem finite_res (PP : Pl E) : Finite (kP PP) :=
  Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

attribute [local instance] finite_res

def IsIndCuspChar (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K] (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ (b : ↥Pg → Fin r → ℕ) (V : ↥Pg → Type) (_ : ∀ PP, AddCommGroup (V PP)) (_ : ∀ PP, Module ℂ (V PP))
    (_ : ∀ PP, FiniteDimensional ℂ (V PP))
    (σ : ∀ PP : ↥Pg, Representation ℂ (blockTri (κ := kP PP.1) (b PP)) (V PP)),
    (∀ PP : ↥Pg, IsCuspDatum (F := kP PP.1) (b PP) (σ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) =
      ∏ PP : ↥Pg, LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) (g PP))

theorem finite_parInd {F : Type} [Field F] [Finite F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := inferInstance

def GenericMultOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K), IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsIndCuspChar Pg r s χ →
      letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
      ∑ h : (P0 Pg r ψ).H, χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K) = (Nat.card (P0 Pg r ψ).H : K)

def GenericMultOneDim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K), IsGenericPsi Pg ψ →
    ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K (G0 Pg r) W),
      IsIndCuspChar Pg r s (fun g => LinearMap.trace K W (τ g)) →
      letI : Fintype (G0 Pg r) := Fintype.ofFinite _
      Module.finrank K (LinearMap.range (τ.asAlgebraHom (lvlIdem (P0 Pg r ψ).H (P0 Pg r ψ).chi))) = 1

example (r : ℕ) : IsIndCuspChar (∅ : Finset (Pl E)) r (RingHom.id ℂ) (fun _ => 1) :=
  ⟨fun _ _ => 0, fun _ => ℂ, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, fun _ => 1,
    fun PP => absurd PP.2 (Finset.notMem_empty _), fun _ => by simp⟩

example (PP : Pl E) : IsCuspDatum (F := kP PP) (fun _ : Fin 1 => 0)
    (Representation.trivial ℂ (blockTri (κ := kP PP) (fun _ : Fin 1 => 0)) ℂ) where
  mono := monotone_const
  irr := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun a => ?_ }
    · have := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top (α := Submodule ℂ ℂ) this
    · rcases eq_bot_or_eq_top a.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  infl := fun _ _ => rfl
  cusp := by
    rintro S ⟨i, j, -, hi, hj⟩
    exact absurd (Subsingleton.elim i j ▸ hi) hj

end GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

open Matrix Formalism.UG ValuativeRel
open scoped TensorProduct
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsUWeilPair)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.LFun (HasSatU)

def str (q : ℂˣ) (n : ℤ) : Multiset ℂˣ := (Multiset.range n.toNat).map fun j : ℕ => q ^ (2 * (j : ℤ) - (n - 1))

section Valued

variable (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))]

def nu (z : Circle) : Eˣ →* Circle :=
  (zpowersHom Circle z⁻¹).comp ((WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation E (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom))

def chi (n : ℕ) : Eˣ →* Circle := nu E (Circle.exp Real.pi ^ n)

variable {E}

variable {n : ℕ}

def IsSelfDualLat (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤ ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, x ⬝ᵥ S *ᵥ (fun i => c (y i)) ∈ intL E

def IsHypFrame (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (P : GL (Fin n) E) :
    Prop :=
  (∀ y : Fin n → E, P.1 *ᵥ y ∈ L ↔ ∀ i, y i ∈ intL E) ∧
    ∃ u : E, Valued.v u = 1 ∧ P.1ᵀ * S * P.1.map c = u • antiJ E n

end Valued

section Local

variable {F : Type} [Field F] {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E]
  (c : E →ₐ[F] E) {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

def HasPh (ϖ : E) (q : ℕ) (s : E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (z : ℂˣ)
    (π : Representation ℂ (UG c J) X) (Φ : Multiset ℂˣ) : Prop :=
  ∃ (P : GL (Fin n) E) (e : UG c J ≃* GU (c : E →+* E) n) (α : Fin (n / 2) → ℂˣ),
    IsHypFrame (c : E →+* E) (s • J) L P ∧ (∀ g, (e g : GL (Fin n) E) = P⁻¹ * (g : GL (Fin n) E) * P) ∧
      HasSatU ϖ q (π.comp e.symm.toMonoidHom) α ∧ Φ = (bcParam n α).map (z⁻¹ * ·)

end Local

def HomNeZero {G Y Z : Type} [Group G] [TopologicalSpace Y] [AddCommGroup Z] [Module ℂ Z]
    (om : G →* Module.End ℂ (Y → ℂ)) (ρ : Representation ℂ G Z) : Prop :=
  ∃ T : SB Y →ₗ[ℂ] Z, T ≠ 0 ∧ ∀ (g : G) (φ φ' : SB Y), (φ' : Y → ℂ) = om g φ → T φ' = ρ g (T φ)

section Res

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def qU : ℂˣ := Units.mk0 ((Nat.card 𝓀[F] : ℕ) : ℂ) (Nat.cast_ne_zero.2 Nat.card_pos.ne')

variable {F} in

def IsUnramAdd (ϖ : F) (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ ∃ x ∈ 𝒪[F], ψ (ϖ⁻¹ * x) ≠ 1

end Res

def SphericalThetaInert : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (ξ : E) (ϖ : Fˣ),
    IsQuad c ξ → IsUnramInv (algebraMap F E ϖ) (c : E →+* E) (Nat.card 𝓀[F]) →
    Odd (Nat.card 𝓀[F]) → 3 < Nat.card 𝓀[F] →
  ∀ ψ : AddChar F ℂ, IsUnramAdd (ϖ : F) ψ →
  ∀ (a b : ℕ), 2 ≤ a → 2 ≤ b →
  ∀ (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E), WeilM.IsHerm c JA → WeilM.IsHerm c JB →
  ∀ (LA : Submodule (intL E) (Fin a → E)) (LB : Submodule (intL E) (Fin b → E)),
    IsSelfDualLat (c : E →+* E) JA LA → IsSelfDualLat (c : E →+* E) (ξ • JB) LB →
  ∀ (κ : Type) [Fintype κ] (d : Darboux (symp c ξ JA JB) κ)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → F) → ℂ)),
    IsUWeilPair c (sbClass F) ψ ξ JA JB d (chi E a) (chi E b) om →
  ∀ (X X' : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ (UG c JA) X) (π' : Representation ℂ (UG c JB) X'),
    π.IsIrreducible → GlobalTheory.PRep.IsSmooth π → π'.IsIrreducible → GlobalTheory.PRep.IsSmooth π' →
    HomNeZero om (extProd π π') →
  ∀ Φ Φ' : Multiset ℂˣ,
    HasPh c (algebraMap F E ϖ) (Nat.card 𝓀[F]) 1 JA LA
      (Circle.toUnits (chi E b (Units.map (algebraMap F E : F →* E) ϖ))) π Φ →
    HasPh c (algebraMap F E ϖ) (Nat.card 𝓀[F]) ξ JB LB
      (Circle.toUnits (chi E a (Units.map (algebraMap F E : F →* E) ϖ))) π' Φ' →
    Φ' + str (qU F) (-((b : ℤ) - a)) = Φ + str (qU F) ((b : ℤ) - a)

example (q : ℂˣ) : str q 1 = {1} ∧ str q 2 = {q, q⁻¹} := by
  constructor
  · simp [str]
  · have : Multiset.range (Int.toNat 2) = {1, 0} := by decide
    rw [str, this]
    simp

example {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] (c : E →+* E) (n : ℕ) :
    IsHypFrame c (antiJ E n) (Submodule.pi Set.univ fun _ => (1 : Submodule (intL E) E)) 1 :=
  ⟨fun y => by
    simp only [Units.val_one, one_mulVec, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩,
  1, map_one _, by simp [Matrix.map_one _ (map_zero c) (map_one c)]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

end

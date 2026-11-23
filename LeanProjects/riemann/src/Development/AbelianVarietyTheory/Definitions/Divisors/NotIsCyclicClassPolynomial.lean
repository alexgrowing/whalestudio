import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HT

def IsWeil (q : ℕ) {L : Type} [Field L] [CharZero L] (π : L) : Prop :=
  IsIntegral ℤ π ∧ ∀ z : ℂ, aeval z (minpoly ℚ π) = 0 → ‖z‖ ^ 2 = q

def IsLieType {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (a : OAct O G) {I : Type} [Fintype I] [DecidableEq I] (φ : I → O →+* R) : Prop :=
  ∃ b : Module.Basis I R (GlobalTheory.Serre.Lie a), ∀ x : O,
    (LinearMap.toMatrix b b (DistribSMul.toLinearMap R (GlobalTheory.Serre.Lie a) x)).charpoly = ∏ i, (X - C (φ i x))

def IsLocalInt (O K : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] : Prop :=
  ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O K ∧ Finite (IsLocalRing.ResidueField O) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal O) O

def IsUnrFrob (O K L : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Field L] [Algebra K L]
    [Algebra O L] (σ : L ≃ₐ[K] L) : Prop :=
  IsLocalInt O K ∧ IsScalarTower O K L ∧
  FiniteDimensional K L ∧ IsGalois K L ∧ (∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) ∧
    ∀ x : integralClosure O L, ∃ y ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O (integralClosure O L)),
      σ x - (x : L) ^ Nat.card (IsLocalRing.ResidueField O) = y

def IsCyclicClass (K L D : Type) [Field K] [Field L] [Algebra K L] [Ring D] [Algebra K D] (σ : L ≃ₐ[K] L)
    (c : K) : Prop :=
  FiniteDimensional K D ∧ Algebra.IsCentral K D ∧ IsSimpleRing D ∧
  FiniteDimensional K L ∧ IsGalois K L ∧ (∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) ∧ c ≠ 0 ∧
  ∃ (N : Type) (_ : AddCommGroup N) (_ : Module L N) (_ : Module K N) (_ : IsScalarTower K L N)
    (_ : FiniteDimensional L N) (ρ : Dᵐᵒᵖ →ₐ[K] Module.End L N) (Ψ : N →+ N),
    Module.finrank L N ^ 2 = Module.finrank K D ∧ (∀ (x : L) (n : N), Ψ (x • n) = σ x • Ψ n) ∧
    (∀ d n, Ψ (ρ d n) = ρ d (Ψ n)) ∧ ∀ n, Ψ^[Module.finrank K L] n = c • n

def HasInv (O K D : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Ring D] [Algebra K D]
    (r : ℚ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Algebra O L) (_ : IsScalarTower O K L) (σ : L ≃ₐ[K] L)
    (ϖ : O) (u : Oˣ) (m z : ℤ), IsUnrFrob O K L σ ∧ Irreducible ϖ ∧
    IsCyclicClass K L D σ (algebraMap O K u * algebraMap O K ϖ ^ m) ∧
    r = (m : ℚ) / (Module.finrank K L : ℚ) + z

def IsPowEnd {p : ℕ} {k : Type} [CommRing k] (q : ℕ) {G : PDivGroup p k} (π : G ⟶ G) : Prop :=
  ∀ (n : ℕ) (x : G.A n), π.app n x = x ^ q

def WittFOn (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (P : PDivGroup p k → Prop) : Prop :=
  ∃ (M : {G // P G} → ModuleCat.{0} (WittVector p k))
    (map : ∀ G H : {G // P G}, (G.1 ⟶ H.1) →+ (M H →ₗ[WittVector p k] M G))
    (red : ∀ G : {G // P G},
      M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.1.RigExt)
    (F : ∀ G : {G // P G}, M G →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M G)
    (V : ∀ G : {G // P G},
      M G →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] M G),
    (∀ G : {G // P G}, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
      Module.finrank (WittVector p k) (M G) = G.1.height ∧
      Function.Surjective (red G) ∧ (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧
      map G G (𝟙 G.1) = LinearMap.id ∧ (∀ m, F G (V G m) = p • m) ∧ (∀ m, V G (F G m) = p • m) ∧
      ∀ (a : ℕ) (π : G.1 ⟶ G.1), (∀ x : k, x ^ p ^ a = x) → IsPowEnd (p ^ a) π →
        ∀ m, map G G π m = (F G)^[a] m) ∧
    (∀ (G H K : {G // P G}) (f : G.1 ⟶ H.1) (g : H.1 ⟶ K.1),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    ∀ (G H : {G // P G}) (f : G.1 ⟶ H.1) (m : M H),
      red G (map G H f m) = PDivGroup.rigExtMap f (red H m) ∧ map G H f (F H m) = F G (map G H f m) ∧
        map G H f (V H m) = V G (map G H f m)

section Examples

open Quaternion

instance quaternion_isCentral : Algebra.IsCentral ℝ ℍ[ℝ] := ⟨fun z hz => by
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨i, i1, i2, i3, i4⟩ : ∃ i : ℍ[ℝ], i.re = 0 ∧ i.imI = 1 ∧ i.imJ = 0 ∧ i.imK = 0 :=
    ⟨⟨0, 1, 0, 0⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨j, j1, j2, j3, j4⟩ : ∃ j : ℍ[ℝ], j.re = 0 ∧ j.imI = 0 ∧ j.imJ = 1 ∧ j.imK = 0 :=
    ⟨⟨0, 0, 1, 0⟩, rfl, rfl, rfl, rfl⟩
  have hi := hz i
  have hj := hz j
  rw [Quaternion.ext_iff] at hi hj
  simp [i1, i2, i3, i4, j1, j2, j3, j4] at hi hj
  refine Algebra.mem_bot.2 ⟨z.re, ?_⟩
  ext <;> simp <;> linarith⟩

end Examples

end GlobalTheory.HT

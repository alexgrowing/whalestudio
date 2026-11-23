import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapE

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def OneAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop := P.valuation E (a - 1) < 1

structure LocSys {A : Type} [CommGroup A] (lam : HeightOneSpectrum (𝓞 F) → Eˣ →* A) (Rm : Set (HeightOneSpectrum (𝓞 F))) : Prop where

  wild : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ),
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → OneAt P (a : E)) → lam v a = 1

  trivF : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), lam v (Units.map (algebraMap F E).toMonoidHom k) = 1

  unr : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Rm → ∀ a : Eˣ,
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → P.valuation E (a : E) = 1) → lam v a = 1

def lamH (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) : Eˣ →* ℂˣ :=
  ∏ P ∈ Formalism.L2.Host.aboveF (L := E) F v, χ.locK P

theorem local_idempotent_mul (v : HeightOneSpectrum (𝓞 F)) (a b : E) :
    (a ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) * (b ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) =
      ((a * b) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) : AfE F E) := by
  have h1 : Formalism.L2.G.sgl F v 1 * Formalism.L2.G.sgl F v 1 = Formalism.L2.G.sgl F v 1 := by rw [← Formalism.L2.G.sgl_mul, one_mul]
  have h2 : Formalism.L2.G.sgl F v 1 * (1 - Formalism.L2.G.sgl F v 1) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
  have h3 : (1 - Formalism.L2.G.sgl F v 1) * Formalism.L2.G.sgl F v 1 = 0 := by rw [_root_.sub_mul, one_mul, h1, sub_self]
  have h4 : (1 - Formalism.L2.G.sgl F v 1) * (1 - Formalism.L2.G.sgl F v 1) = 1 - Formalism.L2.G.sgl F v 1 := by rw [mul_sub, mul_one, h3, sub_zero]
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, h1, h2, h3, h4, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero, zero_add, one_mul]

theorem locId_one (v : HeightOneSpectrum (𝓞 F)) :
    ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) : AfE F E) = 1 := by
  rw [← TensorProduct.tmul_add, add_sub_cancel]
  rfl

variable (E) in

def locId (v : HeightOneSpectrum (𝓞 F)) : Eˣ →* (AfE F E)ˣ where
  toFun a :=
    { val := (a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
      inv := ((a⁻¹ : Eˣ) : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
      val_inv := by rw [local_idempotent_mul, Units.mul_inv, locId_one]
      inv_val := by rw [local_idempotent_mul, Units.inv_mul, locId_one] }
  map_one' := Units.ext (by show ((1 : Eˣ) : E) ⊗ₜ[F] _ + _ = 1; rw [Units.val_one, locId_one])
  map_mul' a b := Units.ext (by
    show ((a * b : Eˣ) : E) ⊗ₜ[F] _ + _ = (_ + _) * (_ + _)
    rw [local_idempotent_mul, Units.val_mul])

def lamX {L : Type} [Field L] (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) : Eˣ →* Lˣ := ξ.comp (locId E v)

end Loc

section G

variable {X : Fields} (Pr : Primes X)

def XiOffG (ξ : Chr X.F X.E X.K) : Prop :=
  ∀ P ∈ Pr.vGs, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal → v ∉ Qprime ξ

end G

section Stmts

def OverTwo : Prop :=
  ∀ X : Fields, X.Ok → ∀ P P' : HeightOneSpectrum (𝓞 X.E), P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F) → P' = P ∨ P' = conjPrime₂ P

def ApproxP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P Q : HeightOneSpectrum (𝓞 E)), P ≠ Q → ∀ t : 𝓞 E,
    ∃ b : 𝓞 E, b ≠ 0 ∧ b - t ∈ P.asIdeal ^ 2 ∧ b - 1 ∈ Q.asIdeal

def AbsSplit : Prop :=
  ∀ X : Fields, X.Ok → ∀ (A : Type) [CommGroup A] (lam : HeightOneSpectrum (𝓞 X.F) → X.Eˣ →* A) (Rm : Set (HeightOneSpectrum (𝓞 X.F))), LocSys lam Rm →
    ∀ (v : HeightOneSpectrum (𝓞 X.F)) (P : HeightOneSpectrum (𝓞 X.E)), P.asIdeal.under (𝓞 X.F) = v.asIdeal → conjPrime₂ P ≠ P →
    ∀ x b : X.Eˣ, OneAt (conjPrime₂ P) (b : X.E) → OneAt P ((b : X.E) / ((x : X.E) / star (x : X.E))) → lam v x = lam v b

def AbsInert : Prop :=
  ∀ X : Fields, X.Ok → ∀ (A : Type) [CommGroup A] (lam : HeightOneSpectrum (𝓞 X.F) → X.Eˣ →* A) (Rm : Set (HeightOneSpectrum (𝓞 X.F))), LocSys lam Rm →
    ∀ (v : HeightOneSpectrum (𝓞 X.F)) (P : HeightOneSpectrum (𝓞 X.E)), P.asIdeal.under (𝓞 X.F) = v.asIdeal → conjPrime₂ P = P → v ∉ Rm →
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2 →
    ∀ x : X.Eˣ, lam v x = 1

def XiSys : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S),
    LocSys (lamX (ξ : Chr F E L)) (Qprime (ξ : Chr F E L))

def XiProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S) (x : Eˣ),
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => lamX (ξ : Chr F E L) v x).Finite ∧ ∏ᶠ v : HeightOneSpectrum (𝓞 F), lamX (ξ : Chr F E L) v x = 1

def XiUnif : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal → v ∉ Qprime (ξ : Chr F E L) →
    ∀ (w : Eˣ) (b : 𝓞 E), (w : E) = (b : E) → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) →
      lamX (ξ : Chr F E L) v w = unifVal (ξ : Chr F E L) P

def XiQ : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (w : Eˣ) (b : 𝓞 E), (w : E) = (b : E) → b - ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 2 →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) →
      lamX (ξ : Chr F E L) v w = qVal (ξ : Chr F E L) P

def XiRes : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ (w : Eˣ) (b : 𝓞 E) (r : (𝓞 E ⧸ P.asIdeal)ˣ), (w : E) = (b : E) → Ideal.Quotient.mk P.asIdeal b = (r : 𝓞 E ⧸ P.asIdeal) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) →
      lamX (ξ : Chr F E L) v w = resChar (ξ : Chr F E L) P r

def HSys : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (Rm : Set (HeightOneSpectrum (𝓞 F))),
    (∀ P, χ.TameAt P) → χ.TrivOn F →
    (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Rm → ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → χ.UnrAt P) →
    LocSys (lamH (F := F) χ) Rm

def HProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ P, P ∉ S → χ.UnrAt P) → ∀ x : Eˣ,
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => lamH (F := F) χ v x).Finite ∧ ∏ᶠ v : HeightOneSpectrum (𝓞 F), lamH (F := F) χ v x = (χ.inf x)⁻¹

def HEval : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Formalism.L2.Host.HChar E), (∀ P, χ.TameAt P) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal → ∀ b : Eˣ,
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → OneAt P' (b : E)) → lamH (F := F) χ v b = χ.locK P b

def HLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)),
    (χ.TameAt P → ∀ a : Eˣ, OneAt P (a : E) → χ.locK P a = 1) ∧
    (χ.UnrAt P → ∀ a : Eˣ, P.valuation E (a : E) = 1 → χ.locK P a = 1) ∧
    (χ.UnrAt P → ∀ a : Eˣ, P.valuation E (a : E) = WithZero.exp (-1 : ℤ) → χ.locK P a = χ.val P)

def HInf : Prop :=
  ∀ X : Fields, X.Ok → ∀ (σ₀ : X.K →+* ℂ) (χ : Formalism.L2.Host.HChar X.E) (n e : X.Tau → ℤ), χ.HasInf (X.embC σ₀) n → (∀ τ, n τ = 2 * -(e τ)) →
    ∀ x : X.Eˣ, ((χ.inf x : ℂˣ) : ℂ) = ∏ τ, σ₀ (X.emb τ ((x : X.E) / star (x : X.E))) ^ (-(e τ))

end Stmts

end Formalism.L2.Ker

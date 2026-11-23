import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemShaKernelIffLocallyTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsingletonComplex
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory

noncomputable section
open NumberField

namespace GlobalTheory.LKTorus.KerOne

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]

def cK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : L →ₐ[K] L :=
  { c.toRingHom with commutes' := hcK }

@[simp] theorem cK_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (x : L) :
    cK c hcK x = c x := rfl

def fixOfK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : Kˣ →* fixU ℚ c where
  toFun a := ⟨Units.map (algebraMap K L : K →* L) a, hcK a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem fixOfK_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (a : Kˣ) :
    (((fixOfK c hcK a : fixU ℚ c) : Lˣ) : L) = algebraMap K L a := rfl

def fromK (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : Kˣ →* H1 ℚ c :=
  (QuotientGroup.mk' (normSub ℚ c)).comp (fixOfK c hcK)

variable (K L) in

def ratNormSub : Subgroup Kˣ :=
  (Units.map (algebraMap ℚ K : ℚ →* K)).range ⊔ GlobalTheory.QuadSymbol.globalNorms K L

section Quad

variable [Algebra.IsQuadraticExtension K L]

def cE (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : L ≃ₐ[K] L :=
  AlgEquiv.ofBijective (cK c hcK) (Algebra.IsAlgebraic.algHom_bijective _)

@[simp] theorem cE_apply (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (x : L) :
    cE c hcK x = c x := rfl

end Quad

end GlobalTheory.LKTorus.KerOne

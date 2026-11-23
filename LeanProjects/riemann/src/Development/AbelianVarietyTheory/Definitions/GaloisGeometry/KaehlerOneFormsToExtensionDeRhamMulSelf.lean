import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD

namespace GlobalTheory.W1

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

def map1 : Ω[K⁄k] →ₗ[K] DR k L :=
  ((ι1 (R := k) (B := L)).restrictScalars K).comp (KaehlerDifferential.map k k K L)

set_option autoImplicit false in
open KaehlerDifferential in
variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] in
theorem _root_.GlobalTheory.W1.kaehlerOneFormsToExtensionDeRham_mul_self (ω : Ω[K⁄k]) :
    _root_.GlobalTheory.W1.map1 k K L ω * _root_.GlobalTheory.W1.map1 k K L ω = 0 := by
  unfold _root_.GlobalTheory.W1.map1 _root_.GlobalTheory.CechDR.ι1
  exact ExteriorAlgebra.ι_sq_zero _

def mapDR : DR k K →ₐ[K] DR k L := ExteriorAlgebra.lift K ⟨map1 k K L, kaehlerOneFormsToExtensionDeRham_mul_self k K L⟩

def IsTrDR (T : DR k L →ₗ[k] DR k K) : Prop :=
  ∀ (b : L) (ω : DR k K), T (b • mapDR k K L ω) = Algebra.trace K L b • ω

open Classical in

def trDR : DR k L →ₗ[k] DR k K := if h : ∃ T, IsTrDR k K L T then h.choose else 0

variable {k K L} {ι : Type}

def trC (c : Finset ι → DR k L) : Finset ι → DR k K := fun s => trDR k K L (c s)

def mapC (c : Finset ι → DR k K) : Finset ι → DR k L := fun s => mapDR k K L (c s)

end GlobalTheory.W1

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) → ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  first | (exact @GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (exact GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (intros; apply GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles  <;> assumption)

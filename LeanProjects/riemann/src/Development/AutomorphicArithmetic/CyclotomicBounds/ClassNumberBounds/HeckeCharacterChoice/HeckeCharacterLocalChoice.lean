import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.IsOpenIsIdeleResOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.IsAntiHecke
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.SplitHom
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.DelRay
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDefs
import Mathlib

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [IsCMField E] [IsGalois K E]

noncomputable def tameFin (E : Type*) [Field E] [NumberField E] [Algebra K E] {ι : Type*}
    [Fintype ι] {M : ℕ} {g : ι → ℕ} (h : ∀ i, g i ∣ M) (ψ : ∀ i, 𝓞 K →+* ZMod (g i))
    (ω : ∀ i, (ZMod (g i))ˣ →* ℂˣ) : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ :=
  ∏ i, ∏ᶠ φ ∈ homsOver E (ψ i), (ω i).comp (placeRed (h i) φ)

private noncomputable abbrev hfc (E : Type*) [Field E] [NumberField E] [IsCMField E] :
    𝓞 E →+* 𝓞 E :=
  (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom

private noncomputable def hfPlace {p : ℕ} (hp : p.Prime) (φ : 𝓞 E →+* ZMod p) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal := RingHom.ker φ
  isPrime := by
    have := Fact.mk hp
    exact RingHom.ker_isPrime φ
  ne_bot := by
    intro h
    have h1 : (p : 𝓞 E) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [h, Ideal.mem_bot] at h1
    exact hp.ne_zero (by exact_mod_cast h1)

end KStar.Choice

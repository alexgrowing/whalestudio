import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ChowHt

namespace PositivityTheory.UnitarySelfGeneration

def ChowFormHeight : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (d N m δ : ℕ) (g : Matrix (Fin N) (Fin m) K)
    (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span K (Set.range g.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ConjCompat A → ∀ (y : Fin N → Ω) (Z : GlobalTheory.ZH.RatModel (𝓞 K) Ω),
    Z.IsCl (fun k => ∑ j, algebraMap K Ω (g j k) * y j) → GlobalTheory.IsArithVar Z.s d →
    ∀ (Φ : MvPolynomial (Fin (d + 1) × Fin N) K), IsChowFormInt (GlobalTheory.CompHt.coneIdeal K y) d δ Φ →
    ∀ (H : LB Z.Z) (hH : H.IsLB) (e : H.ι → Ω), Z.GenTriv H e → ∀ (s : Fin m → H.Sec),
    (∀ k, Z.HasVal e (s k) (∑ j, algebraMap K Ω (g j k) * y j)) →
    ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
      (hdet : ∀ σ, (Mt σ).det ≠ 0)
      (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U),
      (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 =
        GlobalTheory.Adelic.archSize (A σ) x ^ 2) →
      (GlobalTheory.HermLB.fs Z.s hH s hs Mt hdet hc).IsSelfInter ((Module.finrank ℚ K : ℝ) * formHeight δ g A Φ)

end PositivityTheory.UnitarySelfGeneration

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.Published

def FubiniStudyChowHeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N e δ : ℕ) (Y : Scheme.{0}) [IsIntegral Y]
    (i : Y ⟶ PSpace (𝓞 K) N) [IsClosedImmersion i], GlobalTheory.IsArithVar (i ≫ PSpace.str (𝓞 K) N) e →
    ∀ (A : (𝓞 K →+* ℂ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
      (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ,
        A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U)
      (f : MvPolynomial (Fin (e + 1) × Fin (N + 1)) K),
      IsChowFormInt (((i (genericPoint Y) : ProjectiveSpectrum
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (𝓞 K))).asHomogeneousIdeal.toIdeal).map
          (MvPolynomial.map (algebraMap (𝓞 K) K))) e δ f →
      ((GlobalTheory.HermLB.fs (PSpace.str (𝓞 K) N) (GlobalTheory.ProjSpace.O1_isLB (𝓞 K) N) (GlobalTheory.ProjSpace.coord (𝓞 K) N)
          (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) N) A hA hc).pull i rfl).IsSelfInter
        ((Module.finrank ℚ K : ℝ) * formHeight δ (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) K)
          (fun σ => A (σ.comp (algebraMap (𝓞 K) K))) f)

end GlobalTheory.Published

end

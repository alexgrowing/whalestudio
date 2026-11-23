import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisConjInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem rhs_int {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) (g : B.Mat k r) (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    Integrable (JF.integrand Bs F g) Bs.μSS := by
  obtain ⟨hFs, ⟨R, hR⟩, -⟩ := hF
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  set A : ℝ := 9 * ((r : ℝ) + 1) * (n ^ 2 + 1) with hA
  have hthr : JF.TransportedAlt k r A 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    have e : (A - 6 * (r : ℝ) * ((0 : ℕ) : ℝ)) / (9 * ((r : ℝ) + 1)) = n ^ 2 + 1 := by
      rw [hA]; push_cast; field_simp; ring
    rw [← hn, e]; linarith
  have hcc : B.InCC A 0 F := JFxG.cptInCC_G hFs (PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra h0
      exact hgC (hR g hg h0)) A 0
  exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq Bs A F hthr hcc).1 g hg

end Formalism.FourierDecayAlt.P.PBH

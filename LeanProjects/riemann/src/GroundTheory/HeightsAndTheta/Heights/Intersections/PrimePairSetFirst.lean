import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLineFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PushforwardProjLineRankTwo.proof (hPF : PushforwardProjLineFlag.Statement) (hF : FibreDimStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hLine : LineFibreBlocks.Statement) : PushforwardProjLineRankTwo.Statement := by
  unfold PushforwardProjLineRankTwo.Statement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G k₀ L L' N hv hP' hP hk₀ hS hL hLL' hN
  obtain ⟨J, hJ, -⟩ := hR4 G.Φ (FibreBlock κ) (fibreIdx ι' κ)
  have hV : IsProjVarF (fibreIdeal κ G) 1 := hF K ι K' ι' κ v P' d 1 G hv hP' hP
  have h1 := hPF I hI K ι K' ι' κ v P' d 1 G J L L' ![N] hv hP' hP hJ hL hLL'
    (fun j => by fin_cases j; exact hN)
  have h2 := hLine G.Φ (FibreBlock κ) (fibreIdx ι' κ) k₀ (fibreIdeal κ G) J hk₀ hV hS hJ (fibreDeg κ N.a)
  have h3 : (fun j : Fin 1 => fibreDeg κ ((![N] : Fin 1 → HermLine ι') j).a) = ![fibreDeg κ N.a] := by
    funext j
    fin_cases j
    rfl
  rw [h1, h3, h2]
  rfl

end GroundTheory.Heights₂.Heights.Inter

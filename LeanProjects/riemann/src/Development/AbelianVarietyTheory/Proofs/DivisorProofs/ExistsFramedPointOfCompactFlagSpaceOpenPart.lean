import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS

theorem exists_frPt_of_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  intro E _ _ _ H Dw l Xo c Y X K _ z hO
  obtain ⟨a, h⟩ := GlobalTheory.CompHS.exists_chartFr z hO
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨Q, hQ⟩ := h k hz
  refine ⟨algebraMap c.F K, ?_⟩
  have e : (algebraMap c.F K).toAlgebra = a := Algebra.algebra_ext _ _ fun _ => rfl
  rw [e]
  exact ⟨Q, (FlagCover.eq_ptY hQ.lies).symm⟩

end GlobalTheory.CompHS

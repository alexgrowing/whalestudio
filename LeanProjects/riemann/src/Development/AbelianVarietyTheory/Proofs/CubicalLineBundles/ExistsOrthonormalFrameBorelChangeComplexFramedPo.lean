import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem lact_one_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : FD.Frame Ψ r) : FD.lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp [FD.lact, FD.mat]
  rfl

theorem exists_ortho_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U hU y
  obtain ⟨-, -, h3, h4, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨b, hb, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U.X k)).1 x.1 x.2
  have hd := FD.OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  obtain ⟨t', ht'⟩ := (h4 k k x ⟨_, hd⟩).2 ⟨1, (U.X k).Γ.one_mem, b, hb, by rw [lact_one_frame]⟩
  have hi := (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k ⟨_, hd⟩) y).2.2.2 t' ht'
  exact ⟨k, ⟨_, hd⟩, t * t'⁻¹, ho,
    (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k ⟨_, hd⟩) (U.un k x) y).2.2.1 _ _ hi ht⟩

end GlobalTheory.LamT

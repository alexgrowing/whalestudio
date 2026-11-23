import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpaceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemHolSubIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponentStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.UnifFamily

theorem dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) :
    X.dom.Nonempty := by
  choose P _ hP using X.signature
  exact ⟨fun τ => P τ, ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm
    X.Gm_herm).2.1 (fun τ => P τ) hP).1⟩

theorem exists_unf_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∃ U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) ∧ Nonempty (U σ).Comp ∧ (∀ k, ((U σ).X k).dom.Nonempty) ∧ (∀ k la γ, ((U σ).X k).χ la γ = 1) ∧ ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ Formalism.L2.PjFree.CuspFD Xo c U ∧ Formalism.L2.PjFree.CuspMul Xo c U ∧ Formalism.L2.PjFree.SupDef Xo c U ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.regular₂ Xo c U) := by
  intro E _ _ _ H Dw l Xo c hpq
  classical
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  have key : ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Formalism.L2.PjFree.GoodEmb c σ →
      Formalism.L2.PjFree.IsUnf U ∧ Nonempty U.Comp ∧ (∀ k, (U.X k).dom.Nonempty) ∧
      (∀ k la γ, (U.X k).χ la γ = 1) ∧
      ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · obtain ⟨U, h1, h2, h3, -, h5, -⟩ := GlobalTheory.T.exists_frameUniformisation_prescribedSpace GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.T.hasse_norm_theorem_quadratic_extension hB hT
        E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hpq hσ hcc him hφ
      exact ⟨U, fun _ => ⟨h1, h2, fun k => dom_nonempty _, h3, h5⟩⟩
    · obtain ⟨U, -⟩ := GlobalTheory.T.exists_uniformisationData_nonempty_component E H Dw l Xo c hpq σ
      exact ⟨U, fun h => absurd h hσ⟩
  choose U hU using key
  have h₀ : Formalism.L2.PjFree.GoodEmb c (c.F.val : c.F →+* ℂ) := by
    exact rfl
  refine ⟨U, hU, GlobalTheory.T.cuspForms_dominantWeight_finiteDimensional hB E H Dw l Xo c _ U _ h₀ (hU _ h₀).1,
    GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c _ U,
    GlobalTheory.T.supNorm_definite_on_cuspForms_goodEmbedding E H Dw l Xo c _ U (fun σ h => (hU σ h).1), fun hg => ?_⟩
  exact (GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level E H Dw l Xo c hpq hg).2.1 _ U

end GlobalTheory.UnifFamily

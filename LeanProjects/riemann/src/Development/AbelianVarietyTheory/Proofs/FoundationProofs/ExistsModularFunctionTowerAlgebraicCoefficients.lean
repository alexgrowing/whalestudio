import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldIsAlgebraicAdjoinJInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldConstAndQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpansionConvergesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldAnSlGermStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJInvariantInModularFunctionFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExistsGammaLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpUpperTriangularStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := GlobalTheory.T.modularFunctionFractionField_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField Ω ε T
  have hgerm := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hj := GlobalTheory.T.lv_jT_one_and_jT_smul_eq
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).1, sl_mul := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).1, an_sl := GlobalTheory.T.modularFunctionFractionField_an_sl_germ Ω ε T, an_mero := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).2,
            an_exp := fun f => (GlobalTheory.T.modularFunctionFractionField_expansion_converges Ω ε T f).2,
            level := GlobalTheory.T.fractionField_exists_gamma_level Ω ε T, exp_upper := GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular Ω ε T, recip := GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant Ω ε T a ha, bdd := GlobalTheory.T.modularFunctionFractionField_bounded_denominators Ω ε T, sat := GlobalTheory.T.modularFunctionFractionField_saturation Ω ε T,
            mem_q := GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.ExpansionIntegral

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ)
    (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 →
    QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  intro l hl lam N _ M x hM hx hx0
  have hpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hpow : ∀ e : ℕ, ¬ l ∣ M ^ e := fun e h => hM (hl.out.dvd_of_dvd_pow h)
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  refine ⟨⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x hx0, fun k => hsz (M ^ 2) _ (hpow 2) ?_⟩,
    ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => hsz (M ^ 3) _ (hpow 3) ?_⟩⟩
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).1
  · rw [Nat.cast_pow]
    exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N M x k hpos hx).2.1

end GlobalTheory.WpFam.ExpansionIntegral

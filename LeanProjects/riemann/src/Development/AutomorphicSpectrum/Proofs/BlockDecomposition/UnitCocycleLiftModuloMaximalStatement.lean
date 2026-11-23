import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximal
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_cocycle_lift_modulo_maximal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (𝔪 I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ 𝔪 → ∀ (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a)),
      (∀ a, u a * w a - 1 ∈ ext s (𝔪 * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) ∈ ext s I (V a ⊓ V c)) →
      ∃ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
        (∀ a c d, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * (rs X (le₁₂ V a c d) (b i a c) +
            rs X (le₂₃ V a c d) (b i c d) - rs X (le₁₃ V a c d) (b i a d)) ∈ ext s (𝔪 * I) (V a ⊓ V c ⊓ V d)) ∧
        ∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
          (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (𝔪 * I) (V a ⊓ V c) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.Cochain.exists_cochain | exact GlobalTheory.CompanionTheory.FewEq.Cochain.exists_cochain | (intros; apply GlobalTheory.CompanionTheory.FewEq.Cochain.exists_cochain <;> assumption)

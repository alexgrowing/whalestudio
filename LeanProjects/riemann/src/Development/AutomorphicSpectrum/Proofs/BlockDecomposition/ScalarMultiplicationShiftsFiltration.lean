import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LecShift

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  intro O A _ _ _ I γ X q l s 𝒱 i a ha r T x hx
  have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ (r - i).toNat := hx
  have h1 : T.obj.i a ∈ pdP T.obj.δ i := dividedPowerFiltration_map T.obj.compat i ha
  have h2 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ i (r - i).toNat (Ideal.mul_mem_mul h1 hx')
  exact T.obj.pdPow_anti (show r.toNat ≤ i + (r - i).toNat by omega) h2

end GlobalTheory.CompanionTheory.LecShift

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem det_torusPow_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℤ) :
    GeneralLinearGroup.det (torusPow F n l) = uniformizerUnit F ^ (∑ i, l i) := by
  have key : ∀ s : Finset (Fin n),
      ∏ i ∈ s, uniformizerUnit F ^ l i = uniformizerUnit F ^ (∑ i ∈ s, l i) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, _root_.zpow_add]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_torusPow, det_diagonal, ← key Finset.univ]
  simp [Units.coe_prod, Iwasawa.coe_uniformizerUnit, Units.val_zpow_eq_zpow_val]

end GlobalTheory.CompanionTheory.LFUDom

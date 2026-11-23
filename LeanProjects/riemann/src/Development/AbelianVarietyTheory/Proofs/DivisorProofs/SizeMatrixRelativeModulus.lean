import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CellExp

theorem jacquetChar_middleColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N l d : ℕ) (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ)
    (M : GlobalTheory.SmGL.SizeMatrix (fun i : Fin 2 => Fin (b i)) (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l d N j)))
    (f : ∀ i, (Σ j, Fin (M.1 i j)) ≃ Fin (b i)) (z : GlobalTheory.SmGL.Levi k (fun i : Fin 2 => Fin (M.1 i 1))),
    (((GlobalTheory.SmGL.relDeltaHalf k (fun i j => Fin (M.1 i j)))⁻¹ * (GlobalTheory.LeviBlockExponent.pairChar k b χ).comp (GlobalTheory.SmGL.relEmb k f))
        (GlobalTheory.SmGL.swapBlocks k (fun i j => Fin (M.1 i j)) (Pi.mulSingle (1 : Fin 3) z)) : ℂˣ) =
      GlobalTheory.LeviBlockExponent.pairChar k (fun i => M.1 i 1)
        (fun i => χ i * GlobalTheory.SmGL.absPow k ((M.1 i 0 : ℂ) + ((M.1 i 1 : ℂ) - b i) / 2)) z := by
  intro k _ _ _ _ N l d b χ M f z
  have hrow : ∀ i, (M.1 i 0 : ℂ) + M.1 i 1 + M.1 i 2 = b i := by
    intro i
    have := M.2.1 i
    simp only [Fintype.card_fin, Fin.sum_univ_three] at this
    exact_mod_cast this
  have hmod : ∀ i, modExp (fun j : Fin 3 => Fin (M.1 i j)) 1 = (M.1 i 2 : ℤ) - M.1 i 0 := by
    intro i
    simp [modExp, Finset.sum_filter, Fin.sum_univ_three]
  have hsw : ∀ i a, GlobalTheory.SmGL.swapBlocks k (fun i j => Fin (M.1 i j)) (Pi.mulSingle (1 : Fin 3) z) i a =
      (Pi.mulSingle (1 : Fin 3) z : ∀ j, GlobalTheory.SmGL.Levi k (fun i : Fin 2 => Fin (M.1 i j))) a i := fun _ _ => rfl
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, relDeltaHalf_apply, GlobalTheory.LeviBlockExponent.pairChar,
    MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply, relEmb_apply,
    det_leviEmb, deltaHalf_apply, hsw]
  simp only [Fin.prod_univ_three, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    Pi.mulSingle_eq_of_ne (show (2 : Fin 3) ≠ 1 by decide), Pi.one_apply, map_one, one_mul, mul_one, hmod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  have hs : (M.1 i 0 : ℂ) + ((M.1 i 1 : ℂ) - b i) / 2 = -((((M.1 i 2 : ℤ) - M.1 i 0 : ℤ) : ℂ) / 2) := by
    rw [← hrow i]; push_cast; ring
  rw [hs, absPow_neg, MonoidHom.inv_apply]

end GlobalTheory.CellExp

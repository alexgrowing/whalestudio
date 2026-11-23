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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix

namespace GlobalTheory.CuspBlock
theorem tripPlace_val {l d N : ℕ} (h : l + d ≤ N) (p : Σ j : Fin 3, Fin (tripSizes l d N j)) :
    ((tripPlace h p : Fin N) : ℕ) = (∑ j : Fin p.1, tripSizes l d N (Fin.castLE p.1.isLt.le j)) + p.2 := by
  simp [tripPlace, finSigmaFinEquiv_apply]

theorem tripPlace_symm_fst : ∀ {l d N : ℕ} (h : l + d ≤ N) (k : Fin N),
    ((tripPlace h).symm k).1 = if k.val < l then 0 else if k.val < l + d then 1 else 2 := by
  intro l d N h k
  obtain ⟨p, rfl⟩ := (tripPlace h).surjective k
  rw [Equiv.symm_apply_apply, tripPlace_val]
  obtain ⟨j, i⟩ := p
  have hi := i.isLt
  fin_cases j <;>
    simp_all [tripSizes, Fin.sum_univ_succ] <;> (try split_ifs) <;> omega
end GlobalTheory.CuspBlock

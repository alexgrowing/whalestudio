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

noncomputable section

namespace GlobalTheory.CuspBlock

theorem modExp_tripSizes_one (l d N : ℕ) :
    GlobalTheory.SmGL.modExp (fun j : Fin 3 => Fin (tripSizes l d N j)) (1 : Fin 3) =
      ((N - (l + d) : ℕ) : ℤ) - l := by
  unfold GlobalTheory.SmGL.modExp
  simp [Fin.sum_univ_three, Finset.sum_filter, tripSizes]
  congr 2 <;> exact Fintype.card_fin _

theorem deltaHalf_midHom : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (l d N : ℕ), l + d ≤ N → ∀ g : GL (Fin d) k,
    GlobalTheory.SmGL.deltaHalf k (fun j : Fin 3 => Fin (GlobalTheory.CuspBlock.tripSizes l d N j)) (GlobalTheory.CuspBlock.midHom k l d N g) =
      GlobalTheory.SmGL.detChar (Fin d) (GlobalTheory.SmGL.absPow k (((N : ℂ) - 2 * l - d) / 2)) g := by
  intro k _ _ _ _ l d N h g
  rw [GlobalTheory.SmGL.deltaHalf_apply, Fin.prod_univ_three]
  have h0 : (midHom k l d N g) 0 = 1 :=
    Pi.mulSingle_eq_of_ne (M := fun j : Fin 3 => GL (Fin (tripSizes l d N j)) k)
      (i := 1) (i' := 0) (by decide) g
  have h2 : (midHom k l d N g) 2 = 1 :=
    Pi.mulSingle_eq_of_ne (M := fun j : Fin 3 => GL (Fin (tripSizes l d N j)) k)
      (i := 1) (i' := 2) (by decide) g
  have h1 : (midHom k l d N g) 1 = g :=
    Pi.mulSingle_eq_same (M := fun j : Fin 3 => GL (Fin (tripSizes l d N j)) k) 1 g
  rw [h0, h2, h1]
  simp only [map_one, one_mul, mul_one, GlobalTheory.SmGL.detChar_apply]
  rw [modExp_tripSizes_one]
  congr 3
  push_cast [Nat.cast_sub h]
  ring

end GlobalTheory.CuspBlock

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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DoubleCosetFinite

open scoped Pointwise

theorem exists_finset_parab_mul_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (K : Subgroup (GL n k)), IsOpen (K : Set (GL n k)) →
    ∃ Y : Finset (GL n k), ∀ x : GL n k, ∃ p ∈ GlobalTheory.SmGL.parab k e, ∃ y ∈ Y, ∃ κ ∈ K, x = p * y * κ := by
  intro k _ _ _ _ α n _ _ m _ _ _ _ e K hK
  have hKO : IsCompact (KO k n : Set (GL n k)) := GlobalTheory.SplitFlip.isCompact_KO
  obtain ⟨t, ht⟩ := hKO.elim_finite_subcover
    (fun w : (KO k n : Set (GL n k)) => (w : GL n k) • (K : Set (GL n k)))
    (fun w => hK.smul _)
    (fun w hw => Set.mem_iUnion.2 ⟨⟨w, hw⟩, ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨t.map ⟨Subtype.val, Subtype.val_injective⟩, fun x => ?_⟩
  obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul e x
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 (ht hw)
  obtain ⟨κ, hκ, hκw⟩ := Set.mem_smul_set.1 hwi
  refine ⟨p, p.2, i, Finset.mem_map_of_mem _ hi, κ, hκ, ?_⟩
  rw [← hκw, smul_eq_mul, mul_assoc]

end GlobalTheory.DoubleCosetFinite

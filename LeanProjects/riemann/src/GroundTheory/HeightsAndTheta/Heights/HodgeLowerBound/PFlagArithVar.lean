import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGenLeadMinorNeZero
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace FlagArithVar

variable (Ψ : Type) (N : ℕ)

theorem yFl_eq (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = ((genMatFr ℚ Ψ N q.1).submatrix (Fin.castLE (step_le q.2)) A.1).det := by
  rw [yFl, RingHom.map_det]
  congr 1

def leadIdx (q : FlBlock Ψ N) : FlIdx Ψ N q := ⟨Fin.castLE (step_le q.2), Fin.strictMono_castLE _⟩

theorem yFl_lead (q : FlBlock Ψ N) : yFl Ψ N ⟨q, leadIdx Ψ N q⟩ = leadMinor (genMatFr ℚ Ψ N q.1) q.2 := by
  rw [yFl_eq, leadMinor, pivotMinor]
  congr 2
  funext c
  apply Fin.ext
  have := c.isLt
  simp only [leadIdx, Fin.val_castLE, pivotCols]
  split_ifs with h
  · rfl
  · simp only [Fin.val_castLE]; omega

theorem yFl_eq_flagMinor (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = flagMinor (genMatFr ℚ Ψ N q.1) q.2
      ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩ := by
  rw [yFl_eq, flagMinor]
  congr 2
  exact Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2

theorem flagMinor_eq_yFl (τ : Ψ) (i : Fin (N - 1)) (S : PluckerBlocks N N i) :
    flagMinor (genMatFr ℚ Ψ N τ) i S = yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ := by
  rw [yFl_eq, flagMinor]

theorem coneRatios_eq : coneRatios (yFl Ψ N) (leadIdx Ψ N) = Set.range (flagMinorRatio ℚ Ψ N) := by
  ext x
  constructor
  · rintro ⟨⟨q, A⟩, rfl⟩
    refine ⟨(q.1, ⟨q.2, ⟨Finset.univ.image A.1,
      by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩⟩), ?_⟩
    show flagMinor _ _ _ / leadMinor _ _ = yFl Ψ N ⟨q, A⟩ / yFl Ψ N ⟨q, leadIdx Ψ N q⟩
    rw [yFl_lead, yFl_eq_flagMinor]
  · rintro ⟨⟨τ, i, S⟩, rfl⟩
    refine ⟨⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    show yFl Ψ N _ / yFl Ψ N ⟨(τ, i), leadIdx Ψ N (τ, i)⟩ = flagMinor _ _ _ / leadMinor _ _
    rw [yFl_lead, flagMinor_eq_yFl]

theorem toSubfield_adjoin_rat {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    (IntermediateField.adjoin ℚ s).toSubfield = Subfield.closure s := by
  rw [IntermediateField.adjoin_toSubfield]
  refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
    (Subfield.closure_mono Set.subset_union_right)
  rintro _ ⟨q, rfl⟩
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ q

theorem trdeg_int_adjoin {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    Algebra.trdeg ℤ (IntermediateField.adjoin ℚ s) = Algebra.trdeg ℤ (Subfield.closure s) := by
  rw [← (RingEquiv.subfieldCongr (toSubfield_adjoin_rat s)).toIntAlgEquiv.trdeg_eq]
  exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv

theorem trdeg_int_eq_rat {L : Type} [Field L] (I : Algebra ℚ L) :
    Algebra.trdeg ℤ L = @Algebra.trdeg ℚ L _ _ I := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

theorem trdeg_closure_of_rat {E : Type} [Field E] {iQ : Algebra ℚ E} (s : Set E) {c : Cardinal}
    (h : @Algebra.trdeg ℚ (IntermediateField.adjoin ℚ s) _ _ (IntermediateField.adjoin ℚ s).algebra' = c) :
    Algebra.trdeg ℤ (Subfield.closure s) = c := by
  rw [← trdeg_int_adjoin, trdeg_int_eq_rat (IntermediateField.adjoin ℚ s).algebra']
  exact h

end FlagArithVar

open FlagArithVar in

theorem FlagArithVar.proof : FlagArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  have hK : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
  have hhor : IsHorizontal (PFl Ψ N) := horizontal (yFl Ψ N)
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (yFl Ψ N), relevant (yFl Ψ N) _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ (FlIdx Ψ N) (ratioField (yFl Ψ N) (leadIdx Ψ N))
    (ratioPtL (yFl Ψ N) (leadIdx Ψ N)) (birational (yFl Ψ N) _ hc)
    (fun k ↦ ⟨leadIdx Ψ N k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField (yFl Ψ N) (leadIdx Ψ N)) = ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [ratioField, coneRatios_eq, trdeg_int_adjoin]
    exact h
  rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc, hL] at htr
  have : (PFl Ψ N).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) (algebraMap_injective _ hhor)
  rw [hA]
  unfold PFl
  rw [htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree

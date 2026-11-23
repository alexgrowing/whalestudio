import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_join_model

section Trdeg

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem mem_of_mem_adjoin (F : Subfield Ω) (hO : ∀ c : O, algebraMap O Ω c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (F : Set Ω)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem w hw => exact hw
  | algebraMap c => exact hO c
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem trdeg_add (hinj : Function.Injective (algebraMap O Ω)) (F F' : Subfield Ω) (hle : F ≤ F')
    (hO : ∀ c : O, algebraMap O Ω c ∈ F) {r : ℕ} (t : Fin r → Ω) (hind : AlgebraicIndependent F t)
    (hmem : ∀ i, t i ∈ F') (halg : ∀ v ∈ F', IsAlgebraic (IntermediateField.adjoin F (Set.range t)) v) :
    Algebra.trdeg O (Algebra.adjoin O (F' : Set Ω)) =
      Algebra.trdeg O (Algebra.adjoin O (F : Set Ω)) + r := by
  have hU : (F : Set Ω) ∪ (F' : Set Ω) = F' := Set.union_eq_right.2 hle
  have h := AdjoinTrdegAdd.proof O Ω hinj (F : Set Ω) (F' : Set Ω) (Fin r) t
    (by rintro _ ⟨i, rfl⟩; exact hmem i) ?_ ?_
  · rw [hU, Fintype.card_fin] at h
    exact h
  · let f : Algebra.adjoin O (F : Set Ω) →+* F :=
      (Algebra.adjoin O (F : Set Ω)).val.toRingHom.codRestrict F fun a => mem_of_mem_adjoin F hO a.2
    refine AlgebraicIndependent.of_ringHom_of_comp_eq f (RingHom.id Ω) hind ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun w : F => (w : Ω)) hab)
    · ext a; rfl
  · intro a ha
    have h1 : IsAlgebraic (Algebra.adjoin F (Set.range t)) a :=
      IntermediateField.isAlgebraic_adjoin_iff.1 (halg a ha)
    have hsub : ∀ w ∈ Algebra.adjoin F (Set.range t),
        w ∈ Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem w hw => exact Algebra.subset_adjoin (Or.inr hw)
      | algebraMap c => exact Algebra.subset_adjoin (Or.inl c.2)
      | add _ _ _ _ h1 h2 => exact add_mem h1 h2
      | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
    let f : Algebra.adjoin F (Set.range t) →+* Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) :=
      (Algebra.adjoin F (Set.range t)).val.toRingHom.codRestrict _ fun w => hsub w w.2
    refine IsAlgebraic.ringHom_of_comp_eq f (RingHom.id Ω) h1 ?_ ?_
    · intro a b hab
      exact Subtype.ext (congrArg (fun w : Algebra.adjoin O ((F : Set Ω) ∪ Set.range t) => (w : Ω)) hab)
    · ext a; rfl

end Trdeg

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [IsDomain O] [IsDiscreteValuationRing O] [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem comap_eq_ker (y : (Σ k, ι k) → Ω) :
    (pointIdeal O y).comap (C : O →+* MRing ι O) = RingHom.ker (algebraMap O Ω) := by
  ext a
  simp [pointIdeal, RingHom.mem_ker, pointConeMap, MvPolynomial.algebraMap_apply]

theorem dim_eq (hinj : Function.Injective (algebraMap O Ω)) (y : (Σ k, ι k) → Ω)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ringKrullDim (MRing ι O ⧸ pointIdeal O y) =
      (((Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω))).toENat +
        ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
  have h1 := DvrConeDimTrdeg.proof O K ι (pointIdeal O y)
    (GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy)
    (by rw [comap_eq_ker]; exact (RingHom.injective_iff_ker_eq_bot _).1 hinj)
  have h2 : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = _ := ConeTrdegFnField.proof O Ω hinj K ι y hy
  rw [h1, h2, map_add, map_natCast]
  congr 1
  push_cast
  ring

theorem isModelOver_iff (y : (Σ k, ι k) → Ω) (d : ℕ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ↔
      Nonempty K ∧ (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ Function.Injective (algebraMap O Ω) ∧
        (Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω))).toENat = d := by
  have key : ∀ T : ℕ∞, ((T + ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) ↔ T = d := by
    intro T
    have e : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
        (((d : ℕ∞) + ((1 + Fintype.card K : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by
      rw [add_assoc, ← Nat.cast_add]; rfl
    rw [e, WithBot.coe_inj]
    exact ⟨fun h => WithTop.add_right_cancel (ENat.natCast_ne_top _) h, fun h => by rw [h]⟩
  constructor
  · intro h
    have hy := JoinTwoModels.exists_ne_zero y h
    rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
    have hinj : Function.Injective (algebraMap O Ω) := by
      rw [RingHom.injective_iff_ker_eq_bot, ← comap_eq_ker y]
      exact h.2.noTorsion
    refine ⟨h.1, hy, hinj, (key _).1 ?_⟩
    rw [← dim_eq hinj y hy]
    exact h.2.dim
  · rintro ⟨hK, hy, hinj, hT⟩
    rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
    refine ⟨hK, GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy, ?_, ?_⟩
    · rw [comap_eq_ker]; exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
    · rw [dim_eq hinj y hy]
      exact (key _).2 hT

end Model

end PositivityTheory.Xgn.A_join_model

theorem PositivityTheory.Xgn.t_join_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ t : Fin r → Ω, AlgebraicIndependent (fnField O x) t → (∀ i, t i ∈ fnField O (joinCoord x z)) → (∀ v ∈ fnField O (joinCoord x z), IsAlgebraic (IntermediateField.adjoin (fnField O x) (Set.range t)) v) → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) (d + r) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d r hx K' _ _ ι' _ z hz t hind hmem halg
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff (joinCoord x z) (d + r)).2 ⟨inferInstance, ?_, hinj, ?_⟩
  · rintro (k | k)
    · exact hx0 k
    · exact hz k
  · have hle : fnField O x ≤ fnField O (joinCoord x z) := by
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
      · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)
    rw [PositivityTheory.Xgn.A_join_model.trdeg_add hinj _ _ hle
      (fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩)) t hind hmem halg, map_add, map_natCast, hT,
      Nat.cast_add]

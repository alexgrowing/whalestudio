import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassFibreDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

namespace GrassmannianFibreDegree

variable (n p : ℕ) [Fact p.Prime]

theorem span_eq_ker :
    (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) =
      RingHom.ker (Bridge.GeoNum.red (ι := plBlocks 1 1 n) p) :=
  (Bridge.GeoNum.ker_red p).symm

theorem isPrime : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).IsPrime := by
  rw [span_eq_ker]
  exact RingHom.ker_isPrime _

theorem isRelevant : IsRelevant (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) := by
  intro k
  refine ⟨plAnchor 1 n, ?_⟩
  rw [span_eq_ker, RingHom.mem_ker, Bridge.GeoNum.red, map_X]
  exact X_ne_zero _

theorem divSupp_eq :
    divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) = {Ideal.span {C (p : ℤ)}} := by
  have := isPrime n p
  ext W
  simp only [divSupp, bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, isRelevant n p⟩

theorem ringKrullDim_quot :
    ringKrullDim (MRing (plBlocks 1 1 n) ⧸ (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))) =
      ((n + Fintype.card (Fin 1) : ℕ) : WithBot ℕ∞) := by
  rw [span_eq_ker, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (Bridge.GeoNum.red_surjective p)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card ((_ : Fin 1) × PlIdx 1 n) = n + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
    omega
  rw [hc, Fintype.card_fin]

def coordEquiv : (Σ _ : Unit, Fin (n + 1)) ≃ (Σ _ : Fin 1, PlIdx 1 n) :=
  Equiv.ofBijective (GrassmannianLinesProjective.coordMap n)
    ⟨(GrassmannianLinesProjective.isBlockMap n).2.1, GrassmannianLinesProjective.coordMap_surjective n⟩

theorem intNum_bot :
    NumbersDVR.intNum (ZMod p) (⊥ : Ideal (NumbersDVR.MRing (plBlocks 1 1 n) (ZMod p)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have h := FieldNumbers.Relabel.intNum_map_rename (F := ZMod p) (Equiv.ofUnique Unit (Fin 1))
    (coordEquiv n) (fun _ => Subsingleton.elim _ _)
    (⊥ : Ideal (NumbersDVR.MRing (FieldNumbers.ProjIdx n) (ZMod p)))
    (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ))
  rw [Ideal.map_bot] at h
  rw [h]
  exact FieldNumbers.intNum_projectiveSpace (ZMod p) n

theorem geoNum_span :
    geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun _ : Fin n => fun _ : Fin 1 => (1 : ℤ)) = 1 := by
  have := isPrime n p
  have hV : IsMultiProjPrime (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) :=
    ⟨isPrime n p, ⟨{C (p : ℤ)}, fun f hf => ⟨0, by
      rw [Set.mem_singleton_iff.mp hf]
      exact Inter.Conservation.isMultiHomog_C _⟩, rfl⟩, isRelevant n p⟩
  rw [← Bridge.intNum_map_eq_geoNum p n _ hV (Ideal.mem_span_singleton_self _) (ringKrullDim_quot n p)]
  have hb : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))).map
      (MvPolynomial.map (Int.castRingHom (ZMod p))) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr (span_eq_ker n p).le
  rw [hb]
  exact intNum_bot n p

end GrassmannianFibreDegree

open GrassmannianFibreDegree in

theorem GrassFibreDegree.proof : GrassFibreDegree.Statement := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have := isPrime n p
  have hW : (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n))) ∈
      divSupp (⊥ : Ideal (MRing (plBlocks 1 1 n))) (C (p : ℤ)) := by
    rw [divSupp_eq]
    rfl
  have hg : geoNum n (Ideal.span {C (p : ℤ)} : Ideal (MRing (plBlocks 1 1 n)))
      (fun j => ((fun _ : Fin n => fsMulti (plBlocks 1 1 n)) j).a) = 1 :=
    geoNum_span n p
  rw [GrassmannianLinesProjective.grassIdeal_eq_bot]
  unfold vertR
  rw [divSupp_eq, finsum_mem_singleton, if_neg (Inter.Conservation.not_horizontal hp hW),
    Inter.Conservation.charOf_eq hp hW, bot_sup_eq, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self, hg]
  simp

end

end GroundTheory.Heights₂.Heights

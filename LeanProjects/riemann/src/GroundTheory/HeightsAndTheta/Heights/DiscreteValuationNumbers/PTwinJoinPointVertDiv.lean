import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerExtra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorJoinPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)

noncomputable section

namespace JoinPointVerticalDivisor

variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem rename_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') h ∈ mcIdeal R (joinCoord y z) ↔ h ∈ mcIdeal R y := by
  rw [← BundleExamples.joinCoords_eq, ← BundleExamples.joinForm_eq]
  exact joinForm_mem_pointIdeal_iff R y z h

theorem isMultiHomog_rename {R : Type} [CommRing R] {f : MvPolynomial (Σ k, ι k) R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (liftVar ι') f) (Sum.elim a 0) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_joinForm hf

omit [Fintype K'] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in

theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] {R : Type} [CommRing R]
    (b : K → ℕ) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') (weightedHomogeneousComponent (blockWeight ι) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) (Sum.elim b 0)
        (rename (liftVar ι') h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MRing ι R) (Finsupp.weight (blockWeight ι) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hj : IsMultiHomog (rename (liftVar ι') (monomial d r : MRing ι R))
        (Sum.elim (Finsupp.weight (blockWeight ι) d) 0) := isMultiHomog_joinForm hm
    by_cases hb : b = Finsupp.weight (blockWeight ι) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · have hb' : (Sum.elim b 0 : K ⊕ K' → ℕ) ≠ Sum.elim (Finsupp.weight (blockWeight ι) d) 0 :=
        fun e => hb (funext fun k => congrFun e (Sum.inl k))
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hb', map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (liftVar (ι := ι) ι'))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
    exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinPointVerticalDivisor

open JoinPointVerticalDivisor in

theorem JoinPointVerticalDivisor.proof : JoinPointVerticalDivisor.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ y b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k)
    · simpa [pullDeg] using hb k
    · simp [pullDeg]
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O y ≤ Q.comap (rename (liftVar (ι := ι) ptIdx)) := fun h hh =>
      Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O y ptCoord h).mpr hh))
    have hO : (Q.comap (rename (liftVar (ι := ι) ptIdx))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (liftVar ptIdx) u, rename (liftVar ptIdx) v, ⟨_, isMultiHomog_rename hu⟩,
      ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O y ptCoord _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR

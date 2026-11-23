import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalZeroOfMem
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefAddBlock
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]

theorem ker_red_le {W : Ideal (MRing J)} (hpW : (C (p : ℤ) : MRing J) ∈ W) :
    RingHom.ker (Bridge.GeoNum.red (ι := J) p) ≤ W := by
  classical
  rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
  exact hpW

theorem map_red_prime [DecidableEq K] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : MRing J) ∈ W) : NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) := by
  have hker := ker_red_le p hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2

theorem exists_curve_point {W : Ideal (MRing J)} (hW : IsMultiProjPrime W) (hpW : (C (p : ℤ) : MRing J) ∈ W)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (w : (Σ k, J k) → L) (c : ∀ k, J k),
      Algebra.trdeg (ZMod p) L = 1 ∧ (∀ k, w ⟨k, c k⟩ = 1) ∧ mCoordIdeal w = W := by
  classical
  obtain ⟨hQ, hQd⟩ := NefAddBlock.map_red p hW hpW 1 hdim
  have hcm := Bridge.GeoNum.comap_map_eq p (ker_red_le p hpW)
  set Q := W.map (Bridge.GeoNum.red p)
  have := hQ.isPrime
  obtain ⟨n, hn, hrn⟩ := FieldNumbers.FunctionFieldFinite.relDim_eq_trdeg FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) Q hQ
  have hn1 : n = 1 := by
    rw [hQd] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  choose c hc using hQ.relevant
  let π : NumbersDVR.MRing J (ZMod p) →+* FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) :=
    (algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ g, π g = 0 ↔ g ∈ Q := fun g => by
    change algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _ (Ideal.Quotient.mk Q g) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let y₀ : (Σ k, J k) → FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) := fun x => π (X x)
  have hy₀ := hom_eq_aeval (π.comp (Bridge.GeoNum.red p)) y₀ fun x => by simp only [RingHom.comp_apply, map_X, y₀]
  have hyc : ∀ k, y₀ ⟨k, c k⟩ ≠ 0 := fun k h => hc k ((hπ _).1 h)
  have hW₀ : mCoordIdeal y₀ = W := by
    refine le_antisymm (fun g hg => ?_) (le_mCoordIdeal hW.2.1 fun g hg => ?_)
    · rw [← hcm]
      exact (hπ _).1 ((hy₀ g).trans (aeval_zero_of_mem hg))
    · exact (hy₀ g).symm.trans ((hπ _).2 (Ideal.mem_map_of_mem _ hg))
  have hmem : ∀ x, ratioPt y₀ c x ∈ FieldNumbers.homFracDegZero Q := fun x =>
    IntermediateField.subset_adjoin _ _ ⟨_, X x, X ⟨x.1, c x.1⟩, isWeightedHomogeneous_X _ _ x,
      isWeightedHomogeneous_X _ _ (⟨x.1, c x.1⟩ : Σ k, J k), hc x.1, rfl⟩
  refine ⟨FieldNumbers.homFracDegZero Q, inferInstance, inferInstance, fun x => ⟨_, hmem x⟩, c,
    by rw [hn, hn1, Nat.cast_one], fun k => Subtype.ext (div_self (hyc k)), ?_⟩
  rw [← hW₀, mCoordIdeal_ratioPt y₀ c hyc]
  exact (mCoordIdeal_comp (FieldNumbers.homFracDegZero Q).val.toRingHom fun x => ⟨_, hmem x⟩).symm

theorem dim_le {L : Type} [Field L] [Algebra (ZMod p) L] (hL : Algebra.trdeg (ZMod p) L ≤ 1) (w : (Σ k, J k) → L) :
    (C (p : ℤ) : MRing J) ∈ mCoordIdeal w ∧ ∃ m : ℕ, m ≤ 1 + Fintype.card K ∧
      ringKrullDim (NumbersDVR.MRing J (ZMod p) ⧸ (mCoordIdeal w).map (Bridge.GeoNum.red p)) = m := by
  classical
  let Φ : NumbersDVR.MRing J (ZMod p) →ₐ[ZMod p] MvPolynomial K L := aeval fun x => C (w x) * X x.1
  have hΦ : ∀ g : MRing J, mConeMap w g = Φ (Bridge.GeoNum.red p g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f x hf => simp only [map_mul, hf, map_X]; simp [mConeMap, Φ]
  have hcm : mCoordIdeal w = (RingHom.ker Φ).comap (Bridge.GeoNum.red p) := by
    ext g
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hΦ]
    rfl
  have hm : (mCoordIdeal w).map (Bridge.GeoNum.red p) = RingHom.ker Φ := by
    rw [hcm, Ideal.map_comap_of_surjective _ (Bridge.GeoNum.red_surjective p)]
  refine ⟨?_, ?_⟩
  · rw [hcm]
    refine Bridge.GeoNum.ker_le_comap p _ ?_
    rw [Bridge.GeoNum.ker_red]
    exact Ideal.mem_span_singleton_self _
  · rw [hm]
    have : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime _
    obtain ⟨m, h1, h2⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := ZMod p)
      (A := NumbersDVR.MRing J (ZMod p) ⧸ RingHom.ker Φ)
    refine ⟨m, ?_, h1⟩
    have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg Φ) (Ideal.kerLiftAlg_injective Φ)
    rw [h2, ← trdeg_add_eq (ZMod p) L, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast] at h3
    have h4 : (m : Cardinal) ≤ 1 + (Fintype.card K : Cardinal) := h3.trans (by gcongr)
    exact_mod_cast h4

end LevelTowerAlt

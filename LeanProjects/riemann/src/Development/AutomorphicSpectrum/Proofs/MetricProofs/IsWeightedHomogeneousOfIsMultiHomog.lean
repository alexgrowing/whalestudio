import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsGenericCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetSegreConeSmul

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartModel Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (blkW weight_blkW segMono eval_segMono segMono_homog psiPoly eval_psiPoly psiPoly_homog
  comp_mul_homog diag_of_homog)

section Rel

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isWeightedHomogeneous_of_isMultiHomog [DecidableEq K] {s : MRingOver ℂ ι} {a : K → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : IsWeightedHomogeneous (blkW ι) s a := by
  intro d hd
  funext k
  rw [weight_blkW]
  exact hs d (mem_support_iff.2 hd) k

theorem cone_homog [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  refine Ideal.homogeneous_span _ _ ?_
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_of_isMultiHomog ha)⟩

theorem cone_segre_rel {e : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ conePts Q, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  set I := Q ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hI
  have hrad : segMono ι i ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p :=
      fun _ => rfl
    rw [hae]
    by_contra h
    rw [eval_segMono, ReciprocityTheory.ChartRestriction.G.Geo.segre, ← ne_eq, Finset.prod_ne_zero_iff] at h
    have hxm : x ∈ conePts Q := ⟨fun k => ⟨i k, h k (Finset.mem_univ _)⟩, fun f hf => by
      have := hx _ (Ideal.mem_sup_left hf : f ∈ I)
      rwa [hae] at this⟩
    refine hΨ x hxm (funext fun j => ?_)
    have := hx _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩) : psiPoly Ψ j ∈ I)
    rwa [hae, eval_psiPoly] at this
  obtain ⟨r0, hr0⟩ := hrad
  have hmem : segMono ι i ^ (r0 + 1) ∈ I := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hr0
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  let D : K → ℕ := fun _ => r0
  let comp := weightedHomogeneousComponent (R := ℂ) (blkW ι) (D + fun _ => 1)
  have hpow : IsWeightedHomogeneous (blkW ι) (segMono ι i ^ (r0 + 1)) (D + fun _ => 1) := by
    have := (segMono_homog (ι := ι) i).pow (r0 + 1)
    convert this using 1
    funext k; simp [D]
  have hcomp := congrArg comp hab
  rw [map_add, map_sum, weightedHomogeneousComponent_eq_self hpow] at hcomp
  simp only [comp, comp_mul_homog (psiPoly_homog Ψ _)] at hcomp
  have hcd : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ r0 ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (weightedHomogeneousComponent (blkW ι) D (c j)) =
        eval (segre z) G :=
    fun j => diag_of_homog r0 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG hGz using hcd
  refine ⟨r0 + 1, Nat.succ_pos _, G, fun j => by simpa using hG j, fun z hz => ?_⟩
  have h0 := congrArg (eval z) hcomp
  rw [map_add, hz.2 _ (weightedHomogeneousComponent_mem_of_mem _ _ (cone_homog hP) ha _),
    zero_add, map_sum, map_pow, eval_segMono] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hGz, eval_psiPoly, mul_comm]

theorem cone_pow_mem {Q : Ideal (MRingOver ℂ ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : setChartIdeal (conePts Q) σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := cone_segre_rel hP Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [setChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    simp only [f, Gx, map_sub, map_add, map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    simp only [f, map_sub, map_add, map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem cxChartModel {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : CxInt.IsCxVar Q e) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ : CxInt.IsSetGoodProj (conePts Q) Ψ) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ ∧
      ∀ J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  obtain ⟨hK, ⟨hQp, hQh, -⟩, hdimQ⟩ := hQ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQh
  refine ⟨chart_zeroSet hR σ Ψ, fun J hJ => ?_⟩
  have hdim := chart_dim hQp hR hdimQ σ Ψ hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := cone_pow_mem hR hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end Rel

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart

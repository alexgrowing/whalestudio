import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem hessC_finset_sum_mul {D : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) :
    hessC (fun y => ∑ a ∈ s, c a * f a y) z = ∑ a ∈ s, (c a : ℂ) • hessC (f a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_hessC_eq_zero (f := fun _ => (0 : ℝ)) (y := z) 0 (Eventually.of_forall fun _ => rfl)
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => c a * f a y) z := contDiffAt_const.mul (hf a)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ b ∈ s, c b * f b y) z :=
      ContDiffAt.sum fun b _ => contDiffAt_const.mul (hf b)
    simp only [Finset.sum_insert ha]
    rw [hessC_add' _ _ z h1 h2, ih, hessC_const_mul']

theorem mdisc_sum_smul {D : ℕ} {σ : Type*} [Fintype σ] (H : σ → Matrix (Fin D) (Fin D) ℂ)
    (c : Fin D → σ → ℂ) :
    mdisc (fun i => ∑ a, c i a • H a) =
      ∑ w : Fin D → σ, (∏ i, c i (w i)) * mdisc (fun i => H (w i)) := by
  classical
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  rw [← hM, M.map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [M.map_smul_univ, smul_eq_mul]

theorem locDens_sumPot_expand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {σ : Type} [Fintype σ] (P : σ → LocPot X) (c : Fin e → σ → ℝ) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hC : ∀ a, IsTwiceDifferentiableAt A (P a) ((A.chart j).symm y)) :
    locDens A (fun i => sumPot (c i) P) j y =
      ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
  classical
  have hf : ∀ a, ContDiffAt ℝ 2
      (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro a
    have := hC a j ((A.chart j).map_target hy)
    rwa [(A.chart j).right_inv hy] at this
  have hH : ∀ i, hessC (fun y' => (sumPot (c i) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ a, ((c i a : ℝ) : ℂ) •
        hessC (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun i =>
    hessC_finset_sum_mul Finset.univ (c i) _ y hf
  simp only [locDens, maDens, hH]
  rw [mdisc_sum_smul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

theorem mInt_sumPot_expand (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (σ : Type) [Fintype σ] (U : Set X) (P : σ → LocPot X)
    (c : Fin e → σ → ℝ) (g : X → ℝ) (hN : IsNull A Uᶜ)
    (hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (P a) x)
    (hI : ∀ w : Fin e → σ, MIntegrable A (fun i => P (w i)) g) :
    MIntegrable A (fun i => sumPot (c i) P) g ∧
      mInt A (fun i => sumPot (c i) P) g =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * mInt A (fun i => P (w i)) g := by
  classical
  have key : ∀ j, ∀ᵐ y, y ∈ (A.chart j).target →
      locDens A (fun i => sumPot (c i) P) j y =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN j)] with y hy hyt
    have hU : (A.chart j).symm y ∈ U := by
      by_contra h
      exact hy ⟨hyt, h⟩
    exact locDens_sumPot_expand A P c j hyt fun a => hC a _ hU
  refine ⟨fun j K hK hKc => ?_, ?_⟩
  · have h1 : IntegrableOn (fun y => ∑ w : Fin e → σ, (∏ i, c i (w i)) *
        (g ((A.chart j).symm y) * locDens A (fun i => P (w i)) j y)) K :=
      integrable_finsetSum _ fun w _ => (hI w j K hK hKc).const_mul _
    refine Integrable.congr h1 ?_
    filter_upwards [ae_restrict_of_ae (key j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · have h : Nonempty (ChartPartition A) := existsPartition A
    simp only [mInt, dif_pos h, integralWith]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hw : ∀ w : Fin e → σ, IntegrableOn (fun y => (∏ i, c i (w i)) *
        (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A (fun i => P (w i)) j y)) (A.chart j).target := fun w =>
      (integrableOn_weight A h.some _ g (hI w) j).const_mul _
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun w _ => hw w]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (key j),
      ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy hyt
    rw [hy hyt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.PB

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.AmbMetric

variable {k : Type} [CommRing k]

section Calc

variable {P : Scheme.{0}} {q : P ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts q σ}

theorem cInfAt_mul {f g : CxPts q σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_one_sub {f : CxPts q σ → ℝ} (hf : CInfAt f y) : CInfAt (fun z => 1 - f z) y :=
  hf.comp₂ hf (G := fun x => 1 - x.1) (contDiff_const.sub contDiff_fst)

theorem cInfAt_prod {ι : Type} (s : Finset ι) {f : ι → CxPts q σ → ℝ} (hf : ∀ i ∈ s, CInfAt (f i) y) :
    CInfAt (fun z => ∏ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := q) 1 y
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact cInfAt_mul (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Calc

theorem exists_bump {P : Scheme.{0}} {q : P ⟶ Sp k} {N : ℕ} {σ : k →+* ℂ} (R : AnRead q σ N)
    [T2Space (CxPts q σ)] (y : CxPts q σ) (W : Set (CxPts q σ)) (hW : IsOpen W) (hy : y ∈ W) :
    ∃ β : CxPts q σ → ℝ, (∀ z, CInfAt β z) ∧ (∀ z, 0 ≤ β z ∧ β z ≤ 1) ∧ tsupport β ⊆ W ∧
      ∀ᶠ z in 𝓝 y, β z = 1 := by
  classical
  obtain ⟨c, hc⟩ := R.cover y
  set e := (R.chart c).e with he
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
  have hyT : e y ∈ e.target ∩ e.symm ⁻¹' W := ⟨e.map_source hc, by rw [mem_preimage, e.left_inv hc]; exact hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT (e y) hyT
  let β₀ : ContDiffBump (e y) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target ∩ e.symm ⁻¹' W :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e y) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e y) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun v hv => (hcb hv).1)
  have hCsub : C ⊆ e.source ∩ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e.map_target (hcb hv).1, (hcb hv).2⟩
  let β : CxPts q σ → ℝ := fun w => if w ∈ e.source then β₀ (e w) else 0
  have hsupp : Function.support β ⊆ C := by
    intro w hw
    simp only [Function.mem_support, β] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e y) (ε / 2) := by
        rw [← β₀.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport β ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨β, fun z => ?_, fun z => ?_, hts.trans fun w hw => (hCsub hw).2, ?_⟩
  · by_cases hz : z ∈ e.source
    · refine cInfAt_of_chart e.open_source (R.chart c) ?_ hz hz
      refine (β₀.contDiff.contDiffOn (s := e.target ∩ e.symm ⁻¹' e.source)).congr fun v hv => ?_
      have hv1 : e.symm v ∈ e.source := hv.2
      show (if e.symm v ∈ e.source then β₀ (e (e.symm v)) else 0) = β₀ v
      rw [if_pos hv1, e.right_inv hv.1]
    · have hzC : z ∉ C := fun h => hz (hCsub h).1
      refine (cInfAt_const (p := q) 0 z).congr ?_
      filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hzC] with w hw
      by_contra h
      exact hw (hsupp h)
  · simp only [β]
    split_ifs
    · exact ⟨β₀.nonneg, β₀.le_one⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hc, Metric.mem_ball_self (by linarith)⟩] with w hw
    simp only [β, if_pos hw.1]
    exact β₀.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

theorem exists_partition {P : Scheme.{0}} {q : P ⟶ Sp k} {N : ℕ} {σ : k →+* ℂ} (R : AnRead q σ N)
    [CompactSpace (CxPts q σ)] [T2Space (CxPts q σ)] {J : Type} (V : J → Set (CxPts q σ)) (hV : ∀ j, IsOpen (V j))
    (hc : ∀ y, ∃ j, y ∈ V j) :
    ∃ (n : ℕ) (c : Fin n → J) (ρ : Fin n → CxPts q σ → ℝ), (∀ a y, CInfAt (ρ a) y) ∧ (∀ a y, 0 ≤ ρ a y) ∧
      (∀ a, tsupport (ρ a) ⊆ V (c a)) ∧ ∀ y, ∑ a, ρ a y = 1 := by
  classical
  choose j hj using hc
  choose β hβs hβb hβt hβ1 using fun y => exists_bump R y (V (j y)) (hV (j y)) (hj y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : CxPts q σ => interior {y | β x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hβ1 y)⟩)
  let pt : Fin t.card → CxPts q σ := fun a => (t.equivFin.symm a : CxPts q σ)
  let ψ : Fin t.card → CxPts q σ → ℝ := fun a => β (pt a)
  have hsum : ∀ x, ∑ a, ψ a x * ∏ b ∈ Finset.univ with b < a, (1 - ψ b x) = 1 - ∏ a, (1 - ψ a x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun a => j (pt a), fun a x => ψ a x * ∏ b ∈ Finset.univ with b < a, (1 - ψ b x),
    fun a y => ?_, fun a y => ?_, fun a => ?_, fun x => ?_⟩
  · exact cInfAt_mul (hβs _ y) (cInfAt_prod _ fun b _ => cInfAt_one_sub (hβs _ y))
  · exact mul_nonneg (hβb _ y).1 (Finset.prod_nonneg fun b _ => sub_nonneg.2 (hβb _ y).2)
  · exact (tsupport_mul_subset_left (f := ψ a)).trans (hβt (pt a))
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : pt (t.equivFin ⟨u, hu⟩) = u := by simp [pt]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | β u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory.AmbMetric

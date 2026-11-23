import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution

namespace GlobalTheory

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt

namespace Published

def AnalyticLogResolution : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    IsProjective A →
  ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
  ∀ (q : ℕ) (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ),
    (∀ i, IsPotential A (L i) ∧ IsSection A (L i) (t i) ∧ ∃ y ∈ Z, t i y y ≠ 0) →
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : CompactSpace Y) (_ : T2Space Y) (B : FinHolAtlas n Y)
    (μ : Y → X) (_ : HoloMap B A μ) (S : Set X) (r : ℕ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ)
    (J : Finset (Fin r)),
    IsProjective B ∧ Set.range μ = Z ∧ A.IsAnalyticSubset S ∧ Z \ S ⊆ regularLocus A Z n ∧
    Z ⊆ closure (Z \ S) ∧ Set.InjOn μ (μ ⁻¹' S)ᶜ ∧
    (∀ y, y ∉ μ ⁻¹' S → ∀ j, y ∈ (B.chart j).source → ∀ v : Fin n → ℂ,
      fderiv ℂ (fun w => A.chart (chartIdx A (μ y)) (μ ((B.chart j).symm w))) (B.chart j y) v = 0 →
        v = 0) ∧
    μ ⁻¹' S = ⋃ k ∈ J, W k ∧ IsJointSNC B μ L t W e

end Published

namespace AnLogRes

variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem eq_univ_of_interior_nonempty [PreconnectedSpace X] (A : FinHolAtlas d X) {S : Set X}
    (hS : A.IsAnalyticSubset S) (h : (interior S).Nonempty) : S = Set.univ := by
  have hc : IsClosed (interior S) := by
    refine isClosed_of_closure_subset fun x hx => ?_
    obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
    obtain ⟨j, hj⟩ := A.cover x
    have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
      (A.chart j).symm.isOpen_inter_preimage hW
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho (A.chart j x)
      ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hxW⟩
    have hN : IsOpen ((A.chart j).source ∩ A.chart j ⁻¹' Metric.ball (A.chart j x) ε) :=
      (A.chart j).isOpen_inter_preimage Metric.isOpen_ball
    have hxN : x ∈ (A.chart j).source ∩ A.chart j ⁻¹' Metric.ball (A.chart j x) ε :=
      ⟨hj, Metric.mem_ball_self hε⟩
    obtain ⟨p, hpN, hpS⟩ := mem_closure_iff.1 hx _ hN hxN
    have hz : ∀ i, Set.EqOn (f i ∘ (A.chart j).symm) 0 (Metric.ball (A.chart j x) ε) := by
      intro i
      refine ((hf i j).mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected hpN.2 ?_
      have ho' : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (interior S ∩ W)) :=
        (A.chart j).symm.isOpen_inter_preimage (isOpen_interior.inter hW)
      have hpW : p ∈ W := by simpa [(A.chart j).left_inv hpN.1] using (hball hpN.2).2
      filter_upwards [ho'.mem_nhds ⟨(A.chart j).map_source hpN.1, by
        simpa [(A.chart j).left_inv hpN.1] using And.intro hpS hpW⟩] with w hw
      have : (A.chart j).symm w ∈ S ∩ W := ⟨interior_subset hw.2.1, hw.2.2⟩
      rw [hSW] at this
      exact this.2 i
    refine mem_interior.2 ⟨_, fun y hy => ?_, hN, hxN⟩
    have hyW : y ∈ W := by simpa [(A.chart j).left_inv hy.1] using (hball hy.2).2
    have : y ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hyW, fun i => by simpa [(A.chart j).left_inv hy.1] using hz i hy.2⟩
    exact this.1
  exact Set.eq_univ_of_univ_subset
    ((IsClopen.eq_univ ⟨hc, isOpen_interior⟩ h).symm.subset.trans interior_subset)

theorem isIrreducibleAnalytic_univ [ConnectedSpace X] (A : FinHolAtlas d X) :
    IsIrreducibleAnalytic A Set.univ := by
  refine ⟨fun x => ⟨Set.univ, isOpen_univ, trivial, 0, Fin.elim0, fun i => i.elim0, by simp⟩,
    Set.univ_nonempty, fun Z₁ Z₂ h₁ h₂ h => ?_⟩
  by_cases e : Set.univ = Z₁
  · exact Or.inl e
  · refine Or.inr (eq_univ_of_interior_nonempty A h₂ ?_).symm
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 (Ne.symm e)
    refine ⟨x, mem_interior.2 ⟨Z₁ᶜ, fun y hy => ?_, (pushA_isClosed A h₁).isOpen_compl, hx⟩⟩
    exact (h ▸ Set.mem_univ y : y ∈ Z₁ ∪ Z₂).resolve_left hy

end AnLogRes

end GlobalTheory

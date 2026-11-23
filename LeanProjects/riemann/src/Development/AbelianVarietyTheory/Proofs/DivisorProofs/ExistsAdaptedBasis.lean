import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.FlagBasis

theorem exists_coeff {C U : Type} [Field C] [AddCommGroup U] [Module C U] {n : ℕ} (b : Fin n → U) (i : ℕ)
    {y : U} (hy : y ∈ step C b i) : ∃ r : Fin n → C, (∀ j : Fin n, i ≤ j → r j = 0) ∧ ∑ j, r j • b j = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun j hj => Pi.single_eq_of_ne ?_ _, by simp [Pi.single_apply]⟩
    rintro rfl
    exact absurd hk (not_lt.2 hj)
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, fun j hj => by simp [hr j hj, hs j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a • r, fun j hj => by simp [hr j hj], by simp [Finset.smul_sum, smul_smul]⟩

theorem exists_lift {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {La : Submodule O U} (hfg : La.FG)
    {b : Fin n → U} (hb : LinearIndependent C b) (i : Fin n) {a : C} (ha : a ≠ 0) (hLa : a • b i ∈ La) :
    ∃ (w : U) (c : C), c ≠ 0 ∧ w ∈ La ∧ w - c • b i ∈ step C b i ∧
      ∀ x ∈ La, x ∈ step C b (i + 1) → ∃ o : O, x - o • w ∈ step C b i := by
  obtain ⟨c, hc, e, -⟩ := exists_grAt_eq hv hfg b i (hb.notMem_span_image (by simp)) ha
    (Submodule.zero_mem _) (by rwa [add_zero])
  obtain ⟨w, hw, hw'⟩ : c • (step C b i).mkQ (b i) ∈ grAt C La b i :=
    e ▸ Submodule.mem_span_singleton_self _
  have hw'' : (step C b i).mkQ w = c • (step C b i).mkQ (b i) := hw'
  refine ⟨w, c, hc, hw.1, (Submodule.Quotient.eq _).1 hw'', fun x hx hx' => ?_⟩
  have h1 : (step C b i).mkQ x ∈ grAt C La b i := ⟨x, ⟨hx, hx'⟩, rfl⟩
  rw [e, ← hw''] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h1
  exact ⟨o, (Submodule.Quotient.eq _).1 ho.symm⟩

theorem exists_adapted_basis : ∀ (O C U : Type) [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (v : Valuation C ℝ≥0), v.Integers O → ∀ (n : ℕ) (La : Submodule O U), La.FG → ∀ b : Fin n → U, LinearIndependent C b → (∀ j, ∃ a : C, a ≠ 0 ∧ a • b j ∈ La) → ∃ g : Matrix (Fin n) (Fin n) C, (∀ i j, i < j → g i j = 0) ∧ (∀ i, g i i ≠ 0) ∧ IsLatBasis C La fun i => ∑ j, g i j • b j := by
  intro O C U _ _ _ _ _ _ _ v hv n La hfg b hb hLa
  classical
  choose a ha hLa using hLa
  choose w c hc hw hwb hgen using fun i => exists_lift hv hfg hb i (ha i) (hLa i)
  choose r hr hrb using fun i => exists_coeff b _ (hwb i)
  let g : Matrix (Fin n) (Fin n) C := fun i j => r i j + if j = i then c i else 0
  have hg : ∀ i j, i < j → g i j = 0 := fun i j h => by
    simp [g, hr i j h.le, h.ne']
  have hd : ∀ i, g i i ≠ 0 := fun i => by simpa [g, hr i i le_rfl] using hc i
  have hgw : (fun i => ∑ j, g i j • b j) = w := funext fun i => by
    simp [g, add_smul, Finset.sum_add_distrib, hrb]
  have hws : ∀ i : Fin n, w i ∈ step C b (i + 1) := fun i => by
    simpa using Submodule.add_mem _ (step_mono b (Nat.le_succ _) (hwb i))
      (Submodule.smul_mem _ (c i) (mem_step_succ b i))
  refine ⟨g, hg, hd, ?_, ?_⟩
  · have hu : IsUnit g := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ fun i j hij => hg i j hij]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
    exact (Matrix.linearIndependent_rows_iff_isUnit.2 hu).map' (Fintype.linearCombination C b)
      (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hb s t h))
  · rw [hgw]
    refine le_antisymm (le_inf (Submodule.span_le.2 (Set.range_subset_iff.2 hw))
      (Submodule.span_le_restrictScalars O C _)) ?_
    have key : ∀ k, k ≤ n → ∀ x ∈ La, x ∈ step C b k → x ∈ Submodule.span O (Set.range w) := by
      intro k
      induction k with
      | zero =>
        intro _ x _ hx
        rw [step_zero, Submodule.mem_bot] at hx
        exact hx ▸ Submodule.zero_mem _
      | succ k ih =>
        intro hk x hx hx'
        obtain ⟨o, ho⟩ := hgen ⟨k, hk⟩ x hx hx'
        have h1 := ih (Nat.le_of_succ_le hk) _ (La.sub_mem hx (La.smul_mem o (hw _))) ho
        simpa using Submodule.add_mem _ h1
          (Submodule.smul_mem _ o (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
    rintro x ⟨hx, hx'⟩
    exact key n le_rfl x hx (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
      step_mono b (Nat.succ_le_of_lt i.2) (hws i)) hx')

end GlobalTheory.CompHt.FlagBasis

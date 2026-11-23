import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.LinearIndependentRealOfInt

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen

noncomputable section

theorem ReducedBasisBound.short_basis {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (m : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ,
    ∀ b : Fin m → W, LinearIndependent ℝ b → Sep (span ℤ (Set.range b)) lam →
      (gram ℝ b).det ≤ C → ∃ b' : Fin m → W, span ℤ (Set.range b') = span ℤ (Set.range b) ∧
        ∀ i, ‖b' i‖ ≤ R := by
  induction m with
  | zero => exact fun _ _ _ => ⟨0, fun b _ _ _ => ⟨b, rfl, fun i => i.elim0⟩⟩
  | succ m ih =>
    intro lam hlam C
    obtain ⟨g, hg, hgb⟩ := (bounds (W := W) m).1 (lam / 2) (half_pos hlam)
    obtain ⟨R', hR'⟩ := ih (lam / 2) (half_pos hlam) (C / lam ^ 2)
    refine ⟨|R'| + Real.sqrt (C / g), fun b hb hsep hC => ?_⟩
    obtain ⟨v, c, hvL, hv, hlv, hmin, hc, hmemc, hsepc, hdet⟩ := decompose b hb hlam hsep
    have hgc := hgb c hc hsepc
    have hv2 : ‖v‖ ^ 2 ≤ C / g := by
      rw [le_div_iff₀ hg]
      nlinarith [mul_le_mul_of_nonneg_left hgc (sq_nonneg ‖v‖)]
    have hvR : ‖v‖ ≤ Real.sqrt (C / g) := (le_abs_self _).trans (Real.abs_le_sqrt hv2)
    have hcC : (gram ℝ c).det ≤ C / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
      nlinarith [hg.le.trans hgc]
    obtain ⟨c', hc'span, hc'R⟩ := hR' c hc hsepc hcC
    set L := span ℤ (Set.range b) with hL
    have hlift : ∀ i, ∃ y ∈ L, proj v y = c' i ∧ ‖y‖ ≤ ‖c' i‖ + ‖v‖ / 2 := by
      intro i
      have hci : c' i ∈ span ℤ (Set.range c) := hc'span ▸ subset_span ⟨i, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (hmemc _).1 hci
      obtain ⟨y, hyL, hy, hyn⟩ := exists_lift hvL hv hx
      exact ⟨y, hyL, hy.trans hxe, hxe ▸ hyn⟩
    choose y hyL hy hyn using hlift
    refine ⟨Fin.cons v y, le_antisymm ?_ ?_, fun i => ?_⟩
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvL
      · simpa using hyL j
    · intro x hx
      obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun ℤ).1
        (hc'span ▸ (hmemc (proj v x)).2 ⟨x, hx, rfl⟩)
      have hzL : ∑ j, k j • y j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hyL j)
      have h0 : proj v (x - ∑ j, k j • y j) = 0 := by
        rw [map_sub, map_sum, ← hk, sub_eq_zero]
        simp [map_zsmul, hy]
      obtain ⟨n, hn⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin (L.sub_mem hx hzL) h0
      have hxe : x = n • v + ∑ j, k j • y j := by rw [← hn]; abel
      rw [hxe]
      refine add_mem (smul_mem _ _ (subset_span ⟨0, by simp⟩))
        (sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j.succ, by simp⟩))
    · have hs := Real.sqrt_nonneg (C / g)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        linarith [abs_nonneg R']
      · simp only [Fin.cons_succ]
        linarith [hyn j, hc'R j, le_abs_self R']

theorem ReducedBasisBound.proof : ReducedBasisBound.Statement := by
  intro d t c ht
  obtain ⟨R, hR⟩ := ReducedBasisBound.short_basis (W := EuclideanSpace ℝ (Fin d)) d t ht (c ^ 2)
  refine ⟨R, fun L _ _ hmin hcov => ?_⟩
  have hrk : finrank ℤ L = d := by rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
  let e : Basis (Fin d) ℤ L := Module.finBasisOfFinrankEq ℤ L hrk
  have hspan : span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L := by
    rw [show (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L.subtype '' Set.range e by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, e.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli : LinearIndependent ℝ fun i => (e i : EuclideanSpace ℝ (Fin d)) := by
    have h := (e.ofZLatticeBasis ℝ L).linearIndependent
    rwa [show ⇑(e.ofZLatticeBasis ℝ L) = fun i => (e i : EuclideanSpace ℝ (Fin d)) from
      funext fun i => e.ofZLatticeBasis_apply ℝ L i] at h
  have hdet : (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det ≤ c ^ 2 := by
    have h1 := GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram L e
    rcases le_or_gt 0 (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det with h | h
    · rw [← Real.sq_sqrt h, ← h1]
      exact pow_le_pow_left₀ (ZLattice.covolume_pos L).le hcov 2
    · nlinarith [sq_nonneg c]
  have hsep : Sep (span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d)))) t := by
    rw [hspan]; exact hmin
  obtain ⟨b', hb'span, hb'R⟩ := hR _ hli hsep hdet
  rw [hspan] at hb'span
  have htop : ⊤ ≤ span ℝ (Set.range b') := by
    rw [← IsZLattice.span_top (K := ℝ) (L := L), ← hb'span, Submodule.span_span_of_tower]
  have hliR : LinearIndependent ℝ b' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨(Basis.span (hliR.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hb'span), fun i => ?_⟩
  simpa using hb'R i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume

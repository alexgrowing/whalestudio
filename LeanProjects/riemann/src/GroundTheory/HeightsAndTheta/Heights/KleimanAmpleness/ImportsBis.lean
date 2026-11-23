import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

theorem BlockGenOfModel.proof : BlockGenOfModel.Statement := by
  classical
  intro S _ K ι _ Ω _ _ y k₀ hmod j hj k
  set x := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) with hx
  set A := chartRingOver S x (fun _ => j) with hA

  let D : Set A := {d | ∃ b, y ⟨k, b⟩ ≠ 0 ∧ ∀ a, (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b⟩) ∈ A}
  have hI : (Submodule.span A D : Ideal A) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal _ hne
    have hqp : q.IsPrime := hq.isPrime
    have hsame : modelPts S y = modelPts S x := hmod.2
    have hmem : locIn A q ∈ modelPts S x := ⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩
    rw [← hsame] at hmem
    obtain ⟨c, hc, p, hp, hEq⟩ := hmem
    have hr : ∀ a, y ⟨k, a⟩ / y ⟨k, c k⟩ ∈ locIn A q := by
      intro a
      rw [hEq]
      exact (mem_locIn_chart_iff y c p).mpr
        ⟨⟨_, Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩⟩, 1, Ideal.one_notMem p, by simp⟩
    choose nn dd hdd hnd using fun a => (mem_locIn_chart_iff x (fun _ => j) q).mp (hr a)
    have hdq : (∏ a, dd a) ∉ q := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨a, -, ha⟩
      exact hdd a ha
    apply hdq
    apply hIq
    apply Submodule.subset_span
    refine ⟨c k, hc k, fun a => ?_⟩
    rw [hnd a]
    have hda : (dd a : Ω) ≠ 0 := coe_ne_zero_of_notMem x (fun _ => j) q (hdd a)
    have e : ((∏ a', dd a' : A) : Ω) * ((nn a : Ω) / dd a) =
        (nn a : Ω) * ∏ a' ∈ Finset.univ.erase a, (dd a' : Ω) := by
      rw [SubmonoidClass.coe_finsetProd, ← Finset.mul_prod_erase Finset.univ (fun a' => (dd a' : Ω))
        (Finset.mem_univ a)]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _ (nn a).2 (Subalgebra.prod_mem _ fun i _ => (dd i).2)

  have key : ∀ t ∈ (Submodule.span A D : Ideal A), ∃ w : ι k → Ω,
      (∀ a b, y ⟨k, a⟩ * w b ∈ A) ∧ ∑ b, y ⟨k, b⟩ * w b = (t : Ω) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨b, hb, hdb⟩ := hd
      refine ⟨Pi.single b ((d : Ω) / y ⟨k, b⟩), fun a b' => ?_, ?_⟩
      · by_cases h : b' = b
        · subst h
          simp only [Pi.single_eq_same]
          have e : y ⟨k, a⟩ * ((d : Ω) / y ⟨k, b'⟩) = (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b'⟩) := by ring
          rw [e]
          exact hdb a
        · simp only [Pi.single_eq_of_ne h, mul_zero]
          exact Subalgebra.zero_mem _
      · simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
    | zero => exact ⟨0, fun _ _ => by simp, by simp⟩
    | add s t _ _ hs ht =>
      obtain ⟨w, hw, hws⟩ := hs
      obtain ⟨w', hw', hwt⟩ := ht
      refine ⟨w + w', fun a b => ?_, ?_⟩
      · rw [Pi.add_apply, mul_add]
        exact Subalgebra.add_mem _ (hw a b) (hw' a b)
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hws, hwt]
        push_cast
        ring
    | smul r t _ ht =>
      obtain ⟨w, hw, hwt⟩ := ht
      refine ⟨fun b => (r : Ω) * w b, fun a b => ?_, ?_⟩
      · have e : y ⟨k, a⟩ * ((r : Ω) * w b) = (r : Ω) * (y ⟨k, a⟩ * w b) := by ring
        rw [e]
        exact Subalgebra.mul_mem _ r.2 (hw a b)
      · rw [smul_eq_mul, Subalgebra.coe_mul, ← hwt, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
  obtain ⟨w, hw, hsum⟩ := key 1 (by rw [hI]; exact Submodule.mem_top)
  exact ⟨w, hw, by rw [hsum]; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

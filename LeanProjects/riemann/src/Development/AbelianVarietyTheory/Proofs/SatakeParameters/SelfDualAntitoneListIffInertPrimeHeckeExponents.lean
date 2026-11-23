import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

private theorem sorted_list_sign_split (d : List ℤ) (h : d.Pairwise (fun a b => b ≤ a)) :
    d = d.filter (fun x => decide (0 < x)) ++ d.filter (fun x => decide (x = 0)) ++ d.filter (fun x => decide (x < 0)) := by
  induction d with
  | nil => rfl
  | cons x t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hx, ht⟩ := h
    have ih := ih ht
    rcases lt_trichotomy 0 x with hpos | hzero | hneg
    · have h1 : ¬ x = 0 := by omega
      have h2 : ¬ x < 0 := by omega
      rw [List.filter_cons_of_pos (by simp [hpos]), List.filter_cons_of_neg (by simp [h1]),
        List.filter_cons_of_neg (by simp [h2]), List.cons_append, List.cons_append, ← ih]
    · subst hzero
      have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; simpa using hx y hy
      rw [e1, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp),
        List.filter_cons_of_neg (by simp), e1, List.nil_append, List.cons_append, ← ih]
    · have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have e2 : t.filter (fun x => decide (x = 0)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have h1 : ¬ 0 < x := by omega
      have h2 : ¬ x = 0 := by omega
      rw [e1, e2, List.nil_append, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]),
        List.filter_cons_of_pos (by simp [hneg]), e1, e2, List.nil_append, List.nil_append, ← ih]

private theorem flatMap_singleton_natCast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

private theorem label_list_eq_signed (n : ℕ) (s : List ℕ) : labIn n s =
    s.map (fun a : ℕ => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a : ℕ => -(a : ℤ)) := by
  unfold labIn
  show List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s) ++ _ ++
      List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s.reverse) = _
  rw [flatMap_singleton_natCast, flatMap_singleton_natCast]
  simp [List.map_map, Function.comp_def]

theorem labIn_selfDual_iff : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔
    ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  intro n d
  constructor
  · rintro ⟨hlen, hsort, hdual⟩
    have hsplit := sorted_list_sign_split d hsort
    set P := d.filter (fun x => decide (0 < x)) with hPdef
    set Z := d.filter (fun x => decide (x = 0)) with hZdef
    set N := d.filter (fun x => decide (x < 0)) with hNdef
    have hPN : P = (N.map Neg.neg).reverse := by
      have e : P = (dualLab d).filter (fun x => decide (0 < x)) := by rw [hdual]
      rw [e, dualLab, List.filter_reverse, List.filter_map, hNdef]
      congr 2
      apply List.filter_congr
      intro x _
      simp
    have hN : N = P.reverse.map Neg.neg := by
      rw [hPN, List.reverse_reverse, List.map_map]
      simp
    have hZ : Z = List.replicate Z.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨rfl, ?_⟩
      intro b hb
      rw [hZdef] at hb
      simpa using (List.mem_filter.mp hb).2
    have hlenPN : N.length = P.length := by rw [hN, List.length_map, List.length_reverse]
    have hdlen : d.length = P.length + Z.length + N.length := by
      have := congrArg List.length hsplit
      simpa only [List.length_append] using this
    have hposP : ∀ x ∈ P, 0 < x := by
      intro x hx
      rw [hPdef] at hx
      simpa using (List.mem_filter.mp hx).2
    have hcast : (P.map Int.toNat).map (fun a : ℕ => (a : ℤ)) = P := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id P]
      apply List.map_congr_left
      intro x hx
      have := hposP x hx
      simp only [Function.comp_apply, id]
      omega
    refine ⟨P.map Int.toNat, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map]; omega
    · have hPs : P.Pairwise (fun a b => b ≤ a) := hsort.filter _
      rw [List.pairwise_map]
      exact hPs.imp (fun h => Int.toNat_le_toNat h)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := hposP x hx
      omega
    · have hneg : ((P.map Int.toNat).reverse.map fun a : ℕ => -(a : ℤ)) = N := by
        rw [hN]
        conv_rhs => rw [← hcast]
        simp [List.map_reverse, List.map_map, Function.comp_def]
      have hZ' : Z = List.replicate (n - 2 * P.length) 0 := by
        rw [hZ]
        congr 1
        omega
      rw [label_list_eq_signed, hcast, List.length_map, hneg, ← hZ']
      exact hsplit
  · rintro ⟨s, hs, hsort, hpos, rfl⟩
    rw [label_list_eq_signed]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_replicate, List.length_reverse]
      omega
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hsort.imp (fun h => by exact_mod_cast h)
      · rw [List.pairwise_replicate]
        right; exact le_refl _
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [List.eq_of_mem_replicate hb]
        exact_mod_cast Nat.zero_le x
      · rw [List.pairwise_map, List.pairwise_reverse]
        refine hsort.imp (fun h => ?_)
        simp only [neg_le_neg_iff]
        exact_mod_cast h
      · intro a ha b hb
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        have hb0 : -(y : ℤ) ≤ 0 := by simp
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
          have : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
          omega
        · rw [List.eq_of_mem_replicate ha]
          exact hb0
    · simp [dualLab, List.map_append, List.reverse_append, List.map_reverse, List.map_map,
        Function.comp_def, List.map_replicate, List.reverse_replicate]

end GlobalTheory.Hk3

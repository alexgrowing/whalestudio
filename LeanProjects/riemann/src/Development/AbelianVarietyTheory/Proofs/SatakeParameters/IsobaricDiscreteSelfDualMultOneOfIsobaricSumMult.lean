import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SpehRigid

def seg {C : Type} (p : C × ℕ) : Multiset (C × ℤ) :=
  (Multiset.range p.2).map fun a : ℕ => (p.1, (p.2 : ℤ) - 1 - 2 * (a : ℤ))

theorem seg_nodup {C : Type} (p : C × ℕ) : (seg p).Nodup := by
  refine (Multiset.nodup_range _).map ?_
  intro a b h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem mem_seg {C : Type} (p : C × ℕ) (c : C) (e : ℤ) :
    (c, e) ∈ seg p ↔ p.1 = c ∧ ∃ a : ℕ, a < p.2 ∧ (p.2 : ℤ) - 1 - 2 * (a : ℤ) = e := by
  simp only [seg, Multiset.mem_map, Multiset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨h1, a, ha, h2⟩
  · rintro ⟨h1, a, ha, h2⟩
    exact ⟨a, ha, h1, h2⟩

theorem count_seg {C : Type} [DecidableEq C] (p : C × ℕ) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (seg p).count (c, (d : ℤ) - 1) = (seg p).count (c, (d : ℤ) + 1) + if (c, d) = p then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (seg_nodup p), Multiset.count_eq_of_nodup (seg_nodup p)]
  obtain ⟨c', d'⟩ := p
  have e1 : (c, (d : ℤ) - 1) ∈ seg (c', d') ↔ c' = c ∧ d ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  have e2 : (c, (d : ℤ) + 1) ∈ seg (c', d') ↔ c' = c ∧ d + 2 ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d - 2) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  simp only [e1, e2, Prod.mk.injEq]
  by_cases hc : c' = c
  · subst hc
    simp only [true_and]
    split_ifs <;> omega
  · simp [hc, Ne.symm hc]

theorem count_bind_seg {C : Type} [DecidableEq C] (P : Multiset (C × ℕ)) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (P.bind seg).count (c, (d : ℤ) - 1) = (P.bind seg).count (c, (d : ℤ) + 1) + P.count (c, d) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons p P ih =>
    rw [Multiset.cons_bind, Multiset.count_add, Multiset.count_add, ih, count_seg p c d hd, Multiset.count_cons]
    omega

theorem eq_of_bind_seg {C : Type} (P P' : Multiset (C × ℕ)) (h : ∀ p ∈ P, 1 ≤ p.2) (h' : ∀ p ∈ P', 1 ≤ p.2)
    (e : P.bind seg = P'.bind seg) : P = P' := by
  classical
  ext ⟨c, d⟩
  by_cases hd : 1 ≤ d
  · have h1 := count_bind_seg P c d hd
    have h2 := count_bind_seg P' c d hd
    rw [e] at h1
    omega
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hd (h _ hm),
      Multiset.count_eq_zero_of_notMem fun hm => hd (h' _ hm)]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def flat (p : Formalism.BasicNotions.Part A.CG) : List ((Σ a : ℕ, A.CG a) × ℝ) :=
  (List.range p.d).map fun k : ℕ => (⟨p.a, p.π⟩, ((p.d : ℝ) - 1) / 2 - (k : ℝ))

theorem twSum_append (L L' : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    GlobalTheory.RowTie.twSum N A (L ++ L') w = A.lpSum (GlobalTheory.RowTie.twSum N A L w) (GlobalTheory.RowTie.twSum N A L' w) := by
  unfold GlobalTheory.RowTie.twSum
  induction L with
  | nil => rw [List.nil_append, List.foldr_nil, A.lpSum_comm, A.lpSum_zero]
  | cons p L ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, A.lpSum_assoc]

theorem spehLoc_eq (p : Formalism.BasicNotions.Part A.CG) (w : PlE H) :
    spehLoc N A p w = GlobalTheory.RowTie.twSum N A (flat N A p) w := by
  unfold spehLoc GlobalTheory.RowTie.twSum flat
  have hl : (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = (List.range p.d).map (fun a : ℕ => (a : ℝ)) := by
    simp [List.map_eq_flatMap]
  rw [hl, List.foldr_map, List.foldr_map]

theorem isoLoc_eq (P : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) :
    isoLoc N A P w = GlobalTheory.RowTie.twSum N A (P.flatMap (flat N A)) w := by
  induction P with
  | nil => rfl
  | cons p P ih => rw [List.flatMap_cons, twSum_append, ← ih, ← spehLoc_eq]; rfl

def toPair (p : Formalism.BasicNotions.Part A.CG) : (Σ a : ℕ, A.CG a) × ℕ := (⟨p.a, p.π⟩, p.d)

theorem toPair_injective : Function.Injective (toPair N A) :=
  Function.LeftInverse.injective (g := fun q => ⟨q.1.1, q.1.2, q.2⟩) fun _ => rfl

theorem coe_flatMap (P : List (Formalism.BasicNotions.Part A.CG)) :
    Multiset.ofList (P.flatMap (flat N A)) =
      ((Multiset.ofList (P.map (toPair N A))).bind seg).map fun q => (q.1, (q.2 : ℝ) / 2) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind,
      Multiset.map_add]
    congr 1
    unfold seg flat toPair
    rw [Multiset.map_map, ← Multiset.map_coe]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring

theorem isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' he
  have hpos : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ P.flatMap (flat N A), 1 ≤ q.1.1 := by
    intro P hP q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
    exact (hP p hp).1
  have hd : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ Multiset.ofList (P.map (toPair N A)), 1 ≤ q.2 := by
    intro P hP q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hq)
    exact (hP p hp).2.1
  have h1 := hR _ _ (hpos Pa h) (hpos Pa' h') (by simpa only [isoLoc_eq] using he)
  have h2 := Multiset.coe_eq_coe.2 h1
  rw [coe_flatMap, coe_flatMap] at h2
  have hinj : Function.Injective fun q : (Σ a : ℕ, A.CG a) × ℤ => (q.1, (q.2 : ℝ) / 2) := by
    intro q q' e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e1 e2
    refine Prod.ext e1 ?_
    have : (q.2 : ℝ) = q'.2 := by linarith
    exact_mod_cast this
  have h3 := eq_of_bind_seg _ _ (hd Pa h) (hd Pa' h') (Multiset.map_injective hinj h2)
  rw [← Multiset.map_coe, ← Multiset.map_coe] at h3
  exact Multiset.coe_eq_coe.1 (Multiset.map_injective (toPair_injective N A) h3)

end GlobalTheory.SpehRigid

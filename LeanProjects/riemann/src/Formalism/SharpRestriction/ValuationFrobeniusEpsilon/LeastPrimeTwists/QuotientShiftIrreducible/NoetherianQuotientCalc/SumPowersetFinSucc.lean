import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerZeroSectionVanishing

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open Finset

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem sum_powerset_fin_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ I ∈ (univ : Finset (Fin (n + 1))).powerset, f I =
      ∑ J ∈ (univ : Finset (Fin n)).powerset, f (J.image Fin.succ) +
        ∑ J ∈ (univ : Finset (Fin n)).powerset, f (insert 0 (J.image Fin.succ)) := by
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 ((univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j => Fin.succ_ne_zero j
  have hinj : Function.Injective (fun J : Finset (Fin n) => J.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective n)
  rw [hu, Finset.sum_powerset_insert h0, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]

theorem euler_char_all_zero (ts : List (Deg k × R)) : ∀ (F : GMod B R k),
    (∀ p ∈ ts, ∀ x : F.M, p.2 • x = 0) → ∀ m,
      chi ts F m = ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
        (-1 : ℤ) ^ I.card * ((Module.length B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ) := by
  induction ts with
  | nil =>
    intro F _ m
    have : (Finset.univ : Finset (Fin ([] : List (Deg k × R)).length)) = ∅ := rfl
    rw [this, Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty, sub_zero,
      Finset.card_empty, pow_zero, one_mul]
    rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F h m
    have hs : ∀ x : F.M, s • x = 0 := h (d, s) List.mem_cons_self
    have hts : ∀ p ∈ ts, ∀ x : F.M, p.2 • x = 0 := fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [chi_cons_of_zero ts F d s hs m, ih F hts m, ih F hts (m - d)]
    show _ = ∑ I ∈ (Finset.univ : Finset (Fin (ts.length + 1))).powerset,
        (-1 : ℤ) ^ I.card *
          ((Module.length B (F.gr (m - ∑ i ∈ I, (((d, s) :: ts).get i).1))).toNat : ℤ)
    rw [sum_powerset_fin_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    have hsum : ∀ J : Finset (Fin ts.length),
        ∑ i ∈ J.image Fin.succ, (((d, s) :: ts).get i).1 = ∑ j ∈ J, (ts.get j).1 := fun J => by
      rw [Finset.sum_image (fun a _ b _ hab => Fin.succ_injective _ hab)]
      rfl
    have h0 : ∀ J : Finset (Fin ts.length), (0 : Fin (ts.length + 1)) ∉ J.image Fin.succ :=
      fun J => by
        simp only [mem_image, not_exists, not_and]
        exact fun j _ => Fin.succ_ne_zero j
    congr 1
    · refine Finset.sum_congr rfl fun J _ => ?_
      rw [hsum, Finset.card_image_of_injective _ (Fin.succ_injective _)]
    · refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.sum_insert (h0 J), Finset.card_insert_of_notMem (h0 J), hsum,
        Finset.card_image_of_injective _ (Fin.succ_injective _), pow_succ]
      have : m - d - ∑ j ∈ J, (ts.get j).1
          = m - ((((d, s) :: ts).get (0 : Fin (ts.length + 1))).1 + ∑ j ∈ J, (ts.get j).1) := by
        show _ = m - (d + _)
        rw [sub_sub]
      rw [this]
      ring

theorem ruleAll0 : RuleAll0 := fun _ _ ts F h m => euler_char_all_zero ts F h m

end Formalism.MainNotions.V.Pf.V2.Calc

import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

noncomputable section

open Finset

namespace Formalism.L2.SG.TriangularProducts

def bi : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: S, p => if p < s then 0 else 1 + bi S (p - s)

theorem blockIdx_eq_bi : ∀ (L : List (ℂ × ℕ)) (p : ℕ), Formalism.MainNotions.S.blockIdx L p = bi (L.map Prod.snd) p
  | [], _ => rfl
  | (t, s) :: L, p => by
    simp only [Formalism.MainNotions.S.blockIdx, bi, List.map_cons]
    split_ifs
    · rfl
    · rw [blockIdx_eq_bi L (p - s)]

def PS (S : List ℕ) : Finset (ℕ × ℕ) :=
  ((range S.sum) ×ˢ (range S.sum)).filter (fun q => q.1 < q.2 ∧ bi S q.1 = bi S q.2)

theorem prod_tri {M : Type*} [CommMonoid M] (s : ℕ) (f : ℕ × ℕ → M) :
    ∏ q ∈ ((range s) ×ˢ (range s)).filter (fun q => q.1 < q.2), f q = ∏ b ∈ range s, ∏ a ∈ range b, f (a, b) := by
  rw [Finset.prod_filter, Finset.prod_product_right]
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
  omega

theorem prod_block {M : Type*} [CommMonoid M] (F : ℕ → M) (s : ℕ) :
    ∏ q ∈ ((range s) ×ˢ (range s)).filter (fun q => q.1 < q.2), F (q.2 - q.1) = ∏ m ∈ Ico 1 s, F m ^ (s - m) := by
  rw [prod_tri]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.prod_range_succ, ih]
    have hG : ∏ a ∈ range s, F (s - a) = ∏ m ∈ Ico 1 (s + 1), F m := by
      rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
      rw [← Finset.prod_range_reflect (fun j => F (1 + j)) s]
      refine Finset.prod_congr rfl fun a ha => ?_
      simp only [Finset.mem_range] at ha
      congr 1
      omega
    rw [hG]
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; simp
    · have e1 : ∏ m ∈ Ico 1 (s + 1), F m ^ (s + 1 - m) = (∏ m ∈ Ico 1 (s + 1), F m ^ (s - m)) * ∏ m ∈ Ico 1 (s + 1), F m := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun m hm => ?_
        simp only [Finset.mem_Ico] at hm
        rw [← pow_succ]
        congr 1
        omega
      have e2 : ∏ m ∈ Ico 1 (s + 1), F m ^ (s - m) = ∏ m ∈ Ico 1 s, F m ^ (s - m) := by
        rw [Finset.prod_Ico_succ_top (by omega), Nat.sub_self, pow_zero, mul_one]
      rw [e1, e2]

theorem prod_PS {M : Type*} [CommMonoid M] (F : ℕ → M) :
    ∀ S : List ℕ, ∏ q ∈ PS S, F (q.2 - q.1) = (S.map fun s => ∏ m ∈ Ico 1 s, F m ^ (s - m)).prod
  | [] => by simp [PS]
  | s :: S => by
    have hsplit : PS (s :: S) = (((range s) ×ˢ (range s)).filter (fun q => q.1 < q.2)).disjUnion
        ((PS S).image fun q => (q.1 + s, q.2 + s)) (by
          rw [Finset.disjoint_left]
          rintro ⟨a, b⟩ h1 h2
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h1
          simp only [Finset.mem_image, Prod.mk.injEq, Prod.exists] at h2
          obtain ⟨a', b', -, h3, -⟩ := h2
          omega) := by
      ext ⟨a, b⟩
      unfold PS
      rw [Finset.mem_disjUnion, Finset.mem_filter, Finset.mem_filter, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.mk.injEq, List.sum_cons, bi,
        Prod.exists]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab, hbi⟩
        by_cases has : a < s
        · by_cases hbs : b < s
          · exact Or.inl ⟨⟨has, hbs⟩, hab⟩
          · rw [if_pos has, if_neg hbs] at hbi; omega
        · have hbs : ¬ b < s := by omega
          rw [if_neg has, if_neg hbs] at hbi
          exact Or.inr ⟨a - s, b - s, ⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, by omega⟩
      · rintro (⟨⟨ha, hb⟩, hab⟩ | ⟨a', b', ⟨⟨ha', hb'⟩, hab', hbi'⟩, rfl, rfl⟩)
        · refine ⟨⟨by omega, by omega⟩, hab, ?_⟩
          rw [if_pos ha, if_pos hb]
        · refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
          rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel, hbi']
    rw [hsplit, Finset.prod_disjUnion, prod_block, Finset.prod_image (fun x _ y _ h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (by omega) (by omega)), List.map_cons, List.prod_cons]
    congr 1
    rw [← prod_PS F S]
    refine Finset.prod_congr rfl fun q _ => ?_
    congr 1
    omega

theorem prod_rootPat {M : Type*} [CommMonoid M] {r : ℕ} (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (F : ℕ → M) :
    ∏ q ∈ Formalism.MainNotions.S.rootPat γ, F (q.2.val - q.1.val) =
      (γ.1.map fun b => ∏ m ∈ Ico 1 b.2, F m ^ (b.2 - m)).prod := by
  have hsum : (γ.1.map Prod.snd).sum = r + 1 := γ.2.2
  have himg : (Formalism.MainNotions.S.rootPat γ).image (fun q : Fin (r + 1) × Fin (r + 1) => (q.1.val, q.2.val)) =
      PS (γ.1.map Prod.snd) := by
    ext ⟨a, b⟩
    unfold PS
    rw [Finset.mem_image, Finset.mem_filter]
    simp only [Finset.mem_product, Finset.mem_range, hsum, Formalism.MainNotions.S.rootPat, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨a', b', ⟨hab, hbi⟩, rfl, rfl⟩
      refine ⟨⟨a'.isLt, b'.isLt⟩, hab, ?_⟩
      rw [← blockIdx_eq_bi, ← blockIdx_eq_bi]
      exact hbi
    · rintro ⟨⟨ha, hb⟩, hab, hbi⟩
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨hab, ?_⟩, rfl, rfl⟩
      rw [blockIdx_eq_bi, blockIdx_eq_bi]
      exact hbi
  have h1 := prod_PS F (γ.1.map Prod.snd)
  rw [← himg, Finset.prod_image (fun x _ y _ h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext (Fin.ext h.1) (Fin.ext h.2))] at h1
  rw [List.map_map] at h1
  exact h1

end Formalism.L2.SG.TriangularProducts

end

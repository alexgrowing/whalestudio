import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.HermitianGauss

section Fin

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]

noncomputable def pts (B : Submodule R M) : Finset M := Finset.univ.filter (· ∈ B)

@[simp] theorem mem_pts {B : Submodule R M} {x : M} : x ∈ pts B ↔ x ∈ B := by simp [pts]

theorem card_pts (B : Submodule R M) : (pts B).card = Nat.card B := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_pts)

theorem card_pts_pos (B : Submodule R M) : 0 < (pts B).card := Finset.card_pos.mpr ⟨0, mem_pts.mpr B.zero_mem⟩

theorem card_pts_dvd {A B : Submodule R M} (h : A ≤ B) : (pts A).card ∣ (pts B).card := by
  rw [card_pts, card_pts]
  exact AddSubgroup.card_dvd_of_le (show A.toAddSubgroup ≤ B.toAddSubgroup from h)

theorem eq_of_card_pts {A B : Submodule R M} (h : A ≤ B) (hc : (pts B).card ≤ (pts A).card) : A = B := by
  have hs : pts A ⊆ pts B := fun y hy => mem_pts.mpr (h (mem_pts.mp hy))
  have he := Finset.eq_of_subset_of_card_le hs hc
  refine le_antisymm h fun y hy => ?_
  have : y ∈ pts A := by rw [he]; exact mem_pts.mpr hy
  exact mem_pts.mp this

theorem sum_pts_add (B : Submodule R M) (f : M → ℂ) {z : M} (hz : z ∈ B) :
    ∑ y ∈ pts B, f (y + z) = ∑ y ∈ pts B, f y := by
  refine Finset.sum_nbij' (fun y => y + z) (fun y => y - z) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact mem_pts.mpr (B.add_mem (mem_pts.mp ha) hz)
  · intro a ha; exact mem_pts.mpr (B.sub_mem (mem_pts.mp ha) hz)
  · intro a _; exact add_sub_cancel_right a z
  · intro a _; exact sub_add_cancel a z
  · intro a _; rfl

theorem sum_char (B : Submodule R M) (f : M → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) :
    ∑ y ∈ pts B, f y = if ∀ y ∈ B, f y = 1 then ((pts B).card : ℂ) else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl fun y hy => h y (mem_pts.mp hy)]
    simp
  · push Not at h
    obtain ⟨y0, hy0, hne⟩ := h
    have h1 : ∑ y ∈ pts B, f (y + y0) = ∑ y ∈ pts B, f y := sum_pts_add B f hy0
    simp_rw [hf] at h1
    rw [← Finset.sum_mul] at h1
    have h2 : (∑ y ∈ pts B, f y) * (f y0 - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne

theorem finite_quot {D : Submodule R M} {x : M} {P : Ideal R} (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    Finite (R ⧸ P) := by
  have hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a := fun a => Quotient.out_eq a
  refine Finite.of_injective (fun a : R ⧸ P => (Quotient.out a : R) • x) fun a b hab => ?_
  have hab' : (Quotient.out a : R) • x = (Quotient.out b : R) • x := hab
  have h : (Quotient.out a - Quotient.out b : R) ∈ P := by
    rw [← hP, sub_smul, hab', sub_self]
    exact D.zero_mem
  rw [← hout a, ← hout b]
  exact Ideal.Quotient.eq.mpr h

theorem sum_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P)
    {A : Type} [AddCommMonoid A] (f : M → A) :
    ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y = ∑ q : R ⧸ P, ∑ d ∈ pts D, f (d + (Quotient.out q : R) • x) := by
  have hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a := fun a => Quotient.out_eq a
  calc ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y
      = ∑ p ∈ (Finset.univ : Finset (R ⧸ P)) ×ˢ pts D, f (p.2 + (Quotient.out p.1 : R) • x) := by
        symm
        apply Finset.sum_nbij (fun p => p.2 + (Quotient.out p.1 : R) • x)
        · rintro ⟨q, d⟩ hp
          simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_pts] at hp
          exact mem_pts.mpr (Submodule.add_mem_sup hp
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        · rintro ⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 heq
          simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
            Finset.mem_coe, mem_pts] at h1 h2
          have heq' : d1 + (Quotient.out q1 : R) • x = d2 + (Quotient.out q2 : R) • x := heq
          have hq : q1 = q2 := by
            have hm : (Quotient.out q1 - Quotient.out q2 : R) • x ∈ D := by
              have e : (Quotient.out q1 : R) • x - (Quotient.out q2 : R) • x = d2 - d1 := by
                rw [sub_eq_sub_iff_add_eq_add, add_comm]
                exact heq'
              rw [sub_smul, e]
              exact D.sub_mem h2 h1
            rw [← hout q1, ← hout q2]
            exact Ideal.Quotient.eq.mpr ((hP _).mp hm)
          subst hq
          have : d1 = d2 := add_right_cancel heq'
          rw [this]
        · intro y hy
          rw [Finset.mem_coe, mem_pts] at hy
          obtain ⟨d, hd, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
          have hmem : (Quotient.out (Ideal.Quotient.mk P a) - a : R) ∈ P := Ideal.Quotient.eq.mp (hout _)
          refine ⟨(Ideal.Quotient.mk P a, d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x), ?_, ?_⟩
          · simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
              Finset.mem_coe, mem_pts]
            exact D.sub_mem hd ((hP _).mpr hmem)
          · show d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x
                + (Quotient.out (Ideal.Quotient.mk P a) : R) • x = d + a • x
            rw [sub_smul]
            abel
        · intro p _
          rfl
    _ = _ := Finset.sum_product' _ _ (fun q d => f (d + (Quotient.out q : R) • x))

theorem card_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    (pts (D ⊔ Submodule.span R {x})).card = Fintype.card (R ⧸ P) * (pts D).card := by
  have h := sum_sup hP (fun _ => (1 : ℕ))
  simpa [Finset.sum_const, Finset.card_univ] using h

variable {σ : R →+* R} {β : M → M → ℂ}

def perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y))
    (h0 : ∀ y, β 0 y = 1) (B N : Submodule R M) : Submodule R M where
  carrier := {x | x ∈ B ∧ ∀ y ∈ N, β x y = 1}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, fun y hy => by rw [hadd, ha.2 y hy, hb.2 y hy, one_mul]⟩
  zero_mem' := ⟨B.zero_mem, fun y _ => h0 y⟩
  smul_mem' := fun r a ha => ⟨B.smul_mem r ha.1, fun y hy => by rw [hadj]; exact ha.2 _ (N.smul_mem _ hy)⟩

theorem card_perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    {B C N N' : Submodule R M} (hCN : C ≤ N) (hNB : N ≤ B) (hrad : ∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1)
    (hN' : ∀ x, x ∈ N' ↔ x ∈ B ∧ ∀ y ∈ N, β x y = 1) :
    (pts C).card * (pts B).card = (pts N').card * (pts N).card := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have e1 : ∀ y ∈ pts B, ∑ z ∈ pts N, β y z =
      if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0 := fun y _ => sum_char N (β y) (hr y)
  have h1 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts N').card : ℂ) * (pts N).card := by
    rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
    have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by
      ext y
      simp [pts, hN']
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∀ z ∈ pts N, ∑ y ∈ pts B, β y z =
      if ∀ y ∈ B, β y z = 1 then ((pts B).card : ℂ) else 0 := fun z _ =>
    sum_char B (fun y => β y z) (fun a b => hadd a b z)
  have h2 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts C).card : ℂ) * (pts B).card := by
    rw [Finset.sum_comm, Finset.sum_congr rfl e2, ← Finset.sum_filter]
    have hf : (pts N).filter (fun z => ∀ y ∈ B, β y z = 1) = pts C := by
      ext z
      simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hz, h⟩
        exact (hrad z (hNB hz)).mpr fun y hy => by rw [hsym]; exact h y hy
      · intro hz
        exact ⟨hCN hz, fun y hy => by rw [hsym]; exact (hrad z (hNB (hCN hz))).mp hz y hy⟩
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  exact_mod_cast h2.symm.trans h1

theorem quad_add {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (y z : M) :
    β (w • (y + z)) (y + z) = β (w • y) y * β (w • z) z * β z y := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have key : β (w • y) z * β (w • z) y = β z y := by
    rw [hadj w y z, hsym (w • z) y, ← hr, ← add_smul, add_comm (σ w), hw, one_smul, hsym]
  rw [smul_add, hadd, hr, hr, ← key]
  ring

private theorem exists_mem_not_mem_annihilator_maximal_of_lt {C B : Submodule R M} (hCB : C ≤ B) (hne : C ≠ B) :
    ∃ x ∈ B, x ∉ C ∧ ∃ P : Ideal R, P.IsMaximal ∧ ∀ r : R, r • x ∈ C ↔ r ∈ P := by
  have hne' : (pts B \ pts C).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact hne (le_antisymm hCB fun y hy => mem_pts.mp (h (mem_pts.mpr hy)))
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image _ (fun x => (pts (C ⊔ Submodule.span R {x})).card) hne'
  rw [Finset.mem_sdiff, mem_pts, mem_pts] at hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R M x) C
  have hI : ∀ r : R, r ∈ I ↔ r • x ∈ C := fun r => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨x, hx.1, hx.2, I, ?_, fun r => (hI r).symm⟩
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => hx.2 (by simpa using (hI 1).mp h1), fun J r hIJ hr hrJ => ?_⟩
  have hrx : r • x ∈ pts B \ pts C := by
    rw [Finset.mem_sdiff, mem_pts, mem_pts]
    exact ⟨B.smul_mem r hx.1, fun h => hr ((hI r).mpr h)⟩
  have h1 := hmin _ hrx
  have hle : C ⊔ Submodule.span R {r • x} ≤ C ⊔ Submodule.span R {x} := by
    refine sup_le_sup_left ?_ C
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have heq := eq_of_card_pts hle h1
  have hxm : x ∈ C ⊔ Submodule.span R {r • x} := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp hxm
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have h2 : (1 - s * r) ∈ I := by
    rw [hI]
    have e : (1 - s * r) • x = c := by
      rw [sub_smul, one_smul, mul_smul, sub_eq_iff_eq_add]
      exact hcz.symm
    rw [e]
    exact hc
  have h3 := J.add_mem (hIJ h2) (J.mul_mem_left s hrJ)
  simpa using h3

private theorem sum_pts_eq_sum_pts_orth {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) {B N N' : Submodule R M} (hNB : N ≤ B)
    (hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1) (hQ : ∀ n ∈ N, β (w • n) n = 1) :
    ∑ y ∈ pts B, β (w • y) y = ∑ y ∈ pts N', β (w • y) y := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have hN0 : ((pts N).card : ℂ) ≠ 0 := by exact_mod_cast (card_pts_pos N).ne'
  have step1 : ∀ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) = ∑ y ∈ pts B, β (w • y) y :=
    fun n hn => sum_pts_add B (fun y => β (w • y) y) (hNB (mem_pts.mp hn))
  have step2 : ∀ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) =
      β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) := by
    intro y _
    have e : ∀ n ∈ pts N, β (w • (y + n)) (y + n) = β (w • y) y * β y n := by
      intro n hn
      rw [quad_add hσ hw hadd hsym hadj, hQ n (mem_pts.mp hn), mul_one, hsym n y]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, sum_char N (β y) (hr y)]
  apply mul_left_cancel₀ hN0
  calc ((pts N).card : ℂ) * ∑ y ∈ pts B, β (w • y) y
      = ∑ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) := by
        rw [Finset.sum_congr rfl step1, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) := Finset.sum_comm
    _ = ∑ y ∈ pts B, β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) :=
        Finset.sum_congr rfl step2
    _ = ((pts N).card : ℂ) * ∑ y ∈ pts N', β (w • y) y := by
        rw [Finset.mul_sum]
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by
          ext y
          simp [pts, hN']
        rw [hf]
        exact Finset.sum_congr rfl fun y _ => mul_comm _ _

theorem gauss_fin {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (h0 : ∀ y, β 0 y = 1) (n : ℕ) :
    ∀ B C : Submodule R M, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → (pts B).card = n * (pts C).card →
      ∑ y ∈ pts B, β (w • y) y = (pts C).card * lam n ∧ lam n ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro B C hCB hrad hcard
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1 := fun c hc y hy => (hrad c (hCB hc)).mp hc y hy
  have hQC : ∀ c ∈ C, β (w • c) c = 1 := fun c hc => by
    rw [hsym]; exact hC1 c hc _ (B.smul_mem w (hCB hc))
  have hCpos := card_pts_pos C
  by_cases hBC : C = B
  · subst hBC
    have hn : n = 1 := by
      have h1 : n * (pts C).card = 1 * (pts C).card := by rw [← hcard, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hCpos h1
    subst hn
    rw [Finset.sum_congr rfl fun c hc => hQC c (mem_pts.mp hc)]
    simp
  obtain ⟨x, hxB, hxC, P, hPm, hP⟩ := exists_mem_not_mem_annihilator_maximal_of_lt hCB hBC
  haveI : Finite (R ⧸ P) := finite_quot hP
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  set q := Fintype.card (R ⧸ P)
  have hqc : Nat.card (R ⧸ P) = q := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ q := by
    haveI : P.IsMaximal := hPm
    exact Fintype.one_lt_card
  obtain ⟨hlq, hlqσ⟩ := hlam.2 P hPm inferInstance
  rw [hqc] at hlq hlqσ
  set N := C ⊔ Submodule.span R {x}
  have hNcard : (pts N).card = q * (pts C).card := card_sup hP
  have hCN : C ≤ N := le_sup_left
  have hxN : x ∈ N := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hNB : N ≤ B := sup_le hCB (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB)
  set N' := perp hadd hadj h0 B N
  have hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1 := fun y => Iff.rfl
  have hperp := card_perp hadd hsym hCN hNB hrad hN'
  have hCN' : C ≤ N' := fun c hc => (hN' c).mpr ⟨hCB hc, fun z hz => hC1 c hc z (hNB hz)⟩
  have hN'B : N' ≤ B := fun y hy => ((hN' y).mp hy).1
  have hBpos := card_pts_pos B
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hmemN : ∀ z ∈ N, ∃ c ∈ C, ∃ a : R, c + a • x = z := by
    intro z hz
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, hc, a, rfl⟩
  by_cases hiso : ∀ r : R, β x (r • x) = 1
  · have hxN' : x ∈ N' := (hN' x).mpr ⟨hxB, fun z hz => by
      obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
      rw [hr, hiso, mul_one, hsym]
      exact hC1 c hc x hxB⟩
    have hNN' : N ≤ N' :=
      sup_le hCN' (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxN')
    have hQN : ∀ z ∈ N, β (w • z) z = 1 := by
      intro z hz
      obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
      rw [quad_add hσ hw hadd hsym hadj, hQC c hc, one_mul, hsym (a • x) c,
        hC1 c hc _ (B.smul_mem a hxB), mul_one, smul_smul, hadj, smul_smul]
      exact hiso _
    obtain ⟨m, hm⟩ := card_pts_dvd hNN'
    have hn : n = q * q * m := by
      have h1 : (pts C).card * (n * (pts C).card) = q * (pts C).card * m * (q * (pts C).card) := by
        rw [← hcard, hperp, hm, hNcard]
      have h2 : n * ((pts C).card * (pts C).card) = q * q * m * ((pts C).card * (pts C).card) := by
        calc n * ((pts C).card * (pts C).card) = (pts C).card * (n * (pts C).card) := by ring
          _ = q * (pts C).card * m * (q * (pts C).card) := h1
          _ = q * q * m * ((pts C).card * (pts C).card) := by ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hCpos hCpos) h2
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hn; omega
      · exact h
    have hmn : m < n := by
      have h4 : 2 * m ≤ q * q * m := Nat.mul_le_mul_right m (by nlinarith)
      omega
    have hrad' : ∀ y ∈ N', y ∈ N ↔ ∀ z ∈ N', β y z = 1 := by
      intro y hy
      constructor
      · intro hyN z hz
        rw [hsym]
        exact ((hN' z).mp hz).2 y hyN
      · intro h
        have hN'' : ∀ u, u ∈ perp hadd hadj h0 B N' ↔ u ∈ B ∧ ∀ z ∈ N', β u z = 1 := fun u => Iff.rfl
        have h2 := card_perp hadd hsym hCN' hN'B hrad hN''
        have hNN'' : N ≤ perp hadd hadj h0 B N' := fun u hu =>
          (hN'' u).mpr ⟨hNB hu, fun z hz => by rw [hsym]; exact ((hN' z).mp hz).2 u hu⟩
        have hc : (pts (perp hadd hadj h0 B N')).card ≤ (pts N).card := by
          have h3 : (pts (perp hadd hadj h0 B N')).card * (pts N').card = (pts N).card * (pts N').card := by
            rw [← h2, hperp, mul_comm]
          exact (Nat.eq_of_mul_eq_mul_right (card_pts_pos N') h3).le
        have h4 := eq_of_card_pts hNN'' hc
        rw [h4]
        exact (hN'' y).mpr ⟨hN'B hy, h⟩
    obtain ⟨hs, hl⟩ := ih m hmn N' N hNN' hrad' (by rw [hm, mul_comm])
    rw [sum_pts_eq_sum_pts_orth hσ hw hadd hsym hadj hNB hN' hQN, hs, hNcard, hn]
    have hlq2 : lam q * lam q = q := by rw [← sq]; exact hlq
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, hlq2]
      push_cast
      ring
    · rw [map_mul, map_mul, mul_pow, mul_pow, hl, hlq]
      push_cast
      ring
  · push Not at hiso
    obtain ⟨r0, hr0⟩ := hiso
    let χ : R → ℂ := fun t => β x (t • x)
    have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
      simp only [χ]
      rw [add_smul, hr]
    have hχ0 : χ 0 = 1 := by
      simp only [χ]
      rw [zero_smul, hsym]
      exact h0 x
    have hχP : ∀ t ∈ P, χ t = 1 := fun t ht => by
      simp only [χ]
      rw [hsym]
      exact hC1 _ ((hP t).mpr ht) x hxB
    have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
      simp only [χ]
      rw [← hadj, hsym]
    have hσP : ∀ p ∈ P, σ p ∈ P := by
      intro p hp
      by_contra hsp
      obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsp
      apply hr0
      show χ r0 = 1
      have e1 : r0 = r0 * i + σ (σ (r0 * y) * p) := by
        rw [map_mul, hσ]
        linear_combination (-r0) * hyi
      rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), hχσ, hχP _ (P.mul_mem_left _ hp), mul_one]
    obtain ⟨hlqv, hex⟩ := hlqσ hσP
    have hG := NormFormGauss.gauss_quotient σ w hσ hw P hPm inferInstance hσP hex χ hχadd hχ0 hχP hχσ ⟨r0, hr0⟩
    rw [hqc, finsum_eq_sum_of_fintype] at hG
    have hP' : ∀ r, r • x ∈ N' ↔ r ∈ P := by
      intro r
      constructor
      · intro h
        by_contra hrP
        have hsr : σ r ∉ P := fun h' => hrP (by rw [← hσ r]; exact hσP _ h')
        obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsr
        apply hr0
        show χ r0 = 1
        have e1 : r0 = r0 * i + σ r * (y * r0) := by linear_combination (-r0) * hyi
        rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), one_mul]
        simp only [χ]
        rw [← smul_smul, ← hadj]
        exact ((hN' _).mp h).2 _ (N.smul_mem _ hxN)
      · intro hrP
        refine (hN' _).mpr ⟨B.smul_mem r hxB, fun z hz => ?_⟩
        obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
        rw [hr, hC1 _ ((hP r).mpr hrP) c (hCB hc), one_mul, hadj, smul_smul]
        exact hχP _ (P.mul_mem_right a (hσP r hrP))
    have hsupB : N' ⊔ Submodule.span R {x} = B := by
      apply eq_of_card_pts (sup_le hN'B (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB))
      rw [card_sup hP']
      have h1 : (pts B).card * (pts C).card = q * (pts N').card * (pts C).card := by
        rw [mul_comm, hperp, hNcard]
        ring
      exact (Nat.eq_of_mul_eq_mul_right hCpos h1).le
    obtain ⟨m, hm⟩ := card_pts_dvd hCN'
    have hnqm : n = q * m := by
      have h1 : n * (pts C).card * (pts C).card = q * m * (pts C).card * (pts C).card := by
        calc n * (pts C).card * (pts C).card = (pts C).card * (pts B).card := by rw [hcard]; ring
          _ = (pts N').card * (pts N).card := hperp
          _ = q * m * (pts C).card * (pts C).card := by rw [hm, hNcard]; ring
      exact Nat.eq_of_mul_eq_mul_right hCpos (Nat.eq_of_mul_eq_mul_right hCpos h1)
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hnqm; omega
      · exact h
    have hmn : m < n := by
      have h4 : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq2
      omega
    have hrad' : ∀ y ∈ N', y ∈ C ↔ ∀ z ∈ N', β y z = 1 := by
      intro y hy
      constructor
      · intro hyC z hz
        exact hC1 y hyC z (hN'B hz)
      · intro h
        refine (hrad y (hN'B hy)).mpr fun b hb => ?_
        rw [← hsupB] at hb
        obtain ⟨d, hd, u, hu, rfl⟩ := Submodule.mem_sup.mp hb
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [hr, h d hd, one_mul]
        exact ((hN' y).mp hy).2 _ (N.smul_mem a hxN)
    obtain ⟨hs, hl⟩ := ih m hmn N' C hCN' hrad' (by rw [hm, mul_comm])
    have hsum : ∑ y ∈ pts B, β (w • y) y = (∑ d ∈ pts N', β (w • d) d) *
        ∑ q' : R ⧸ P, χ (w * (Quotient.out q' : R) * σ (Quotient.out q' : R)) := by
      rw [← hsupB, sum_sup hP', Finset.sum_comm, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun q' _ => ?_
      have hdN' := mem_pts.mp hd
      rw [quad_add hσ hw hadd hsym hadj, hsym ((Quotient.out q' : R) • x) d,
        ((hN' d).mp hdN').2 _ (N.smul_mem _ hxN), mul_one]
      congr 1
      simp only [χ]
      rw [hsym, hadj, smul_smul, smul_smul]
      congr 2
      ring
    rw [hsum, hs, hG, hnqm, ← hlqv]
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      push_cast
      ring
    · rw [map_mul, mul_pow, hl, hlq]
      push_cast
      ring

end Fin

theorem gauss_hermitian : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  intro R X _ _ _ σ w hσ hw lam hlam β hadd hsym hadj B C hCB hrad n t htB huniq
  have hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1 := fun c hc y hy => (hrad c (hCB hc)).mp hc y hy
  let C' : Submodule R B := C.comap B.subtype
  have hC' : ∀ a : B, a ∈ C' ↔ (a : X) ∈ C := fun a => Iff.rfl
  let e : Fin n → B ⧸ C' := fun k => Submodule.Quotient.mk ⟨t k, htB k⟩
  have he : Function.Bijective e := by
    constructor
    · intro k l hkl
      have hkl' : (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk ⟨t l, htB l⟩ := hkl
      have h1 : t k - t l ∈ C := by
        have h2 := (Submodule.Quotient.eq C').mp hkl'
        rw [hC'] at h2
        simpa using h2
      obtain ⟨k', _, hk'⟩ := huniq (t k) (htB k)
      exact (hk' k (by show t k - t k ∈ C; rw [sub_self]; exact C.zero_mem)).trans (hk' l h1).symm
    · intro u
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective C' u
      obtain ⟨k, hk, -⟩ := huniq y y.2
      refine ⟨k, ?_⟩
      show (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk y
      rw [Submodule.Quotient.eq, hC', Submodule.coe_sub]
      have h2 : t k - (y : X) = -((y : X) - t k) := by abel
      show t k - (y : X) ∈ C
      rw [h2]
      exact C.neg_mem hk
  haveI : Finite (B ⧸ C') := Finite.of_surjective e he.2
  letI : Fintype (B ⧸ C') := Fintype.ofFinite _
  have hout : ∀ u : B ⧸ C', Submodule.Quotient.mk (Quotient.out u) = u := fun u => Quotient.out_eq u
  have hdesc : ∀ a ∈ B, ∀ a' ∈ B, a - a' ∈ C → ∀ b ∈ B, β a b = β a' b := by
    intro a _ a' _ h b hb
    calc β a b = β (a' + (a - a')) b := by congr 1; abel
      _ = β a' b := by rw [hadd, hC1 _ h b hb, mul_one]
  let β' : B ⧸ C' → B ⧸ C' → ℂ := fun u v => β (Quotient.out u : B) (Quotient.out v : B)
  have hrep : ∀ a : B, ((Quotient.out (Submodule.Quotient.mk a : B ⧸ C') : B) : X) - a ∈ C := by
    intro a
    have h1 := (Submodule.Quotient.eq C').mp (hout (Submodule.Quotient.mk a))
    rw [hC'] at h1
    simpa using h1
  have hβ' : ∀ a b : B, β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = β a b := by
    intro a b
    calc β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
        = β a (Quotient.out (Submodule.Quotient.mk b : B ⧸ C') : B) :=
          hdesc _ (Quotient.out (Submodule.Quotient.mk a : B ⧸ C')).2 _ a.2 (hrep a) _
            (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2
      _ = β (Quotient.out (Submodule.Quotient.mk b : B ⧸ C') : B) a := hsym _ _
      _ = β b a := hdesc _ (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2 _ b.2 (hrep b) _ a.2
      _ = β a b := hsym _ _
  have hadd' : ∀ u v z : B ⧸ C', β' (u + v) z = β' u z * β' v z := by
    intro u v z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective C' z
    rw [← Submodule.Quotient.mk_add, hβ', hβ', hβ', Submodule.coe_add, hadd]
  have hsym' : ∀ u v : B ⧸ C', β' u v = β' v u := by
    intro u v
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [hβ', hβ', hsym]
  have hadj' : ∀ (r : R) (u v : B ⧸ C'), β' (r • u) v = β' u (σ r • v) := by
    intro r u v
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hβ', hβ', Submodule.coe_smul,
      Submodule.coe_smul, hadj]
  have h0' : ∀ v : B ⧸ C', β' 0 v = 1 := by
    intro v
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [← Submodule.Quotient.mk_zero C', hβ', Submodule.coe_zero]
    exact hC1 0 C.zero_mem b b.2
  have hrad' : ∀ u ∈ (⊤ : Submodule R (B ⧸ C')), u ∈ (⊥ : Submodule R (B ⧸ C')) ↔
      ∀ v ∈ (⊤ : Submodule R (B ⧸ C')), β' u v = 1 := by
    intro u _
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, hC', hrad a a.2]
    constructor
    · intro h v _
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
      rw [hβ']
      exact h b b.2
    · intro h y hy
      have h1 := h (Submodule.Quotient.mk ⟨y, hy⟩) Submodule.mem_top
      rwa [hβ'] at h1
  have hpt : pts (⊤ : Submodule R (B ⧸ C')) = Finset.univ := by
    ext
    simp [pts]
  have hpb : pts (⊥ : Submodule R (B ⧸ C')) = {0} := by
    ext
    simp [pts]
  have hcard : (pts (⊤ : Submodule R (B ⧸ C'))).card = n * (pts (⊥ : Submodule R (B ⧸ C'))).card := by
    rw [hpt, hpb, Finset.card_singleton, mul_one, Finset.card_univ, ← Fintype.card_of_bijective he,
      Fintype.card_fin]
  obtain ⟨hs, hl⟩ := gauss_fin (w := w) hσ hw hlam hadd' hsym' hadj' h0' n ⊤ ⊥ bot_le hrad' hcard
  refine ⟨?_, hl⟩
  rw [hpt, hpb, Finset.card_singleton] at hs
  have h1 : ∑ k, β (w • t k) (t k) = ∑ u : B ⧸ C', β' (w • u) u := by
    calc ∑ k, β (w • t k) (t k) = ∑ k, β' (w • e k) (e k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          show β (w • t k) (t k) = β' (w • Submodule.Quotient.mk ⟨t k, htB k⟩) (Submodule.Quotient.mk ⟨t k, htB k⟩)
          rw [← Submodule.Quotient.mk_smul, hβ']
          rfl
      _ = ∑ u : B ⧸ C', β' (w • u) u := he.sum_comp (fun u => β' (w • u) u)
  rw [h1, hs]
  simp

end GlobalTheory.HermitianGauss

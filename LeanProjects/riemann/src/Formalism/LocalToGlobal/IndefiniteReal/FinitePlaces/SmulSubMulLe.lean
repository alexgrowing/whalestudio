import Mathlib
import Lemmata.MiscLemmasC.Imports

set_option linter.style.haveILetI false

noncomputable section

open Finset

namespace Formalism.IndefR.Fin.Four

variable {W : Type*} [AddCommGroup W]

def smulSub (k : ℕ) (H : AddSubgroup W) : AddSubgroup W := H.map (nsmulAddMonoidHom k)

theorem mem_smulSub {k : ℕ} {H : AddSubgroup W} {x : W} : x ∈ smulSub k H ↔ ∃ u ∈ H, k • u = x := by
  simp [smulSub, AddSubgroup.mem_map]

theorem smulSub_mul_le (k j : ℕ) (H : AddSubgroup W) : smulSub (k * j) H ≤ smulSub k H := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_smulSub.1 hx
  exact mem_smulSub.2 ⟨j • u, H.nsmul_mem hu j, by rw [smul_smul]⟩

abbrev Qt (k : ℕ) (H : AddSubgroup W) : Type _ := ↥H ⧸ (smulSub k H).addSubgroupOf H

def IsInv (k : ℕ) (H : AddSubgroup W) (g : W → ℂ) : Prop := ∀ t ∈ H, ∀ u ∈ H, g (t + k • u) = g t

def avg (k : ℕ) (H : AddSubgroup W) (g : W → ℂ) : ℂ :=
  (Nat.card (Qt k H) : ℂ)⁻¹ * ∑ᶠ q : Qt k H, g ((q.out : H) : W)

theorem out_mk (k : ℕ) (H : AddSubgroup W) (x : H) :
    ∃ u ∈ H, ((((QuotientAddGroup.mk x : Qt k H)).out : H) : W) + k • u = (x : W) := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : Qt k H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h
  refine ⟨u, hu, ?_⟩
  rw [hux]
  push_cast
  abel

theorem IsInv.mk_eq {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) {x y : H}
    (hxy : (QuotientAddGroup.mk x : Qt k H) = QuotientAddGroup.mk y) : g x = g y := by
  have h := QuotientAddGroup.eq.1 hxy
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h
  have : (y : W) = x + k • u := by rw [hux]; push_cast; abel
  rw [this, hg _ x.2 u hu]

theorem IsInv.out_mk {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (x : H) :
    g (((QuotientAddGroup.mk x : Qt k H).out : H) : W) = g x :=
  hg.mk_eq (QuotientAddGroup.out_eq' _)

theorem IsInv.mul {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (j : ℕ) : IsInv (k * j) H g := by
  intro t ht u hu
  rw [← smul_smul]
  exact hg t ht _ (H.nsmul_mem hu j)

theorem avg_eq_sum (k : ℕ) (H : AddSubgroup W) [Fintype (Qt k H)] (g : W → ℂ) :
    avg k H g = (Fintype.card (Qt k H) : ℂ)⁻¹ * ∑ q : Qt k H, g ((q.out : H) : W) := by
  rw [avg, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]

theorem avg_comp_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by
  first | exact Bl.SecondBlockLemmaD.goal1 .. | (apply Bl.SecondBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaD.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaD.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaD.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaD.goal1 <;> first | assumption | infer_instance)

theorem avg_mul (k j : ℕ) (H : AddSubgroup W) [Finite (Qt k H)] [Finite (Qt (k * j) H)] (g : W → ℂ)
    (hg : IsInv k H g) : avg (k * j) H g = avg k H g := by
  classical
  let _ := Fintype.ofFinite (Qt k H)
  let _ := Fintype.ofFinite (Qt (k * j) H)
  let π : Qt (k * j) H →+ Qt k H :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id H) (by
      intro x hx
      simp only [AddSubgroup.mem_comap, AddMonoidHom.id_apply, AddSubgroup.mem_addSubgroupOf] at hx ⊢
      exact smulSub_mul_le k j H hx)
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x => exact ⟨QuotientAddGroup.mk x, rfl⟩
  have key : ∀ q : Qt (k * j) H, g ((q.out : H) : W) = g (((π q).out : H) : W) := by
    intro q
    have : π q = QuotientAddGroup.mk q.out := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [this, hg.out_mk]
  rw [avg_eq_sum, avg_eq_sum]
  simp_rw [key]
  exact avg_comp_surj π hπ (fun b => g ((b.out : H) : W))

open Classical in

def integ (H : AddSubgroup W) (g : W → ℂ) : ℂ :=
  if h : ∃ k, 0 < k ∧ IsInv k H g then avg h.choose H g else 0

section Integ

variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin

theorem integ_eq {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) : integ H g = avg k H g := by
  have h : ∃ k, 0 < k ∧ IsInv k H g := ⟨k, hk, hg⟩
  rw [integ, dif_pos h]
  obtain ⟨hk0, hg0⟩ := h.choose_spec
  haveI := hfin _ hk0
  haveI := hfin _ hk
  haveI := hfin _ (Nat.mul_pos hk0 hk)
  haveI := hfin _ (Nat.mul_pos hk hk0)
  rw [← avg_mul h.choose k H g hg0, ← avg_mul k h.choose H g hg, Nat.mul_comm]

omit hfin in
theorem IsInv.congr {k : ℕ} {g g' : W → ℂ} (hg : IsInv k H g) (h : ∀ t ∈ H, g t = g' t) : IsInv k H g' := by
  intro t ht u hu
  rw [← h _ ht, ← h _ (H.add_mem ht (H.nsmul_mem hu k)), hg t ht u hu]

omit hfin in
theorem avg_congr (k : ℕ) {g g' : W → ℂ} (h : ∀ t ∈ H, g t = g' t) : avg k H g = avg k H g' := by
  rw [avg, avg]
  congr 1
  exact finsum_congr fun q => h _ (q.out : H).2

theorem integ_congr {g g' : W → ℂ} (h : ∀ t ∈ H, g t = g' t) : integ H g = integ H g' := by
  by_cases hg : ∃ k, 0 < k ∧ IsInv k H g
  · obtain ⟨k, hk, hgk⟩ := hg
    rw [integ_eq hfin hk hgk, integ_eq hfin hk (hgk.congr h), avg_congr k h]
  · have hg' : ¬ ∃ k, 0 < k ∧ IsInv k H g' := by
      rintro ⟨k, hk, hgk⟩
      exact hg ⟨k, hk, hgk.congr fun t ht => (h t ht).symm⟩
    rw [integ, dif_neg hg, integ, dif_neg hg']

omit hfin in
theorem IsInv.add {k k' : ℕ} {g g' : W → ℂ} (hg : IsInv k H g) (hg' : IsInv k' H g') :
    IsInv (k * k') H (fun t => g t + g' t) := by
  have h1 := hg.mul k'
  have h2 := hg'.mul k
  rw [Nat.mul_comm] at h2
  intro t ht u hu
  simp only [h1 t ht u hu, h2 t ht u hu]

omit hfin in
theorem IsInv.cmul {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) (c : ℂ) : IsInv k H (fun t => c * g t) := by
  intro t ht u hu
  simp only [hg t ht u hu]

theorem integ_cmul {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) (c : ℂ) :
    integ H (fun t => c * g t) = c * integ H g := by
  classical
  rw [integ_eq hfin hk (hg.cmul c), integ_eq hfin hk hg]
  haveI := hfin _ hk
  letI := Fintype.ofFinite (Qt k H)
  rw [avg_eq_sum, avg_eq_sum, ← Finset.mul_sum]
  ring

omit hfin in
theorem IsInv.shift {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    IsInv k H (fun t => g (t + v)) := by
  intro t ht u hu
  simp only
  rw [add_right_comm, hg _ (H.add_mem ht hv) u hu]

theorem integ_shift {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    integ H (fun t => g (t + v)) = integ H g := by
  classical
  rw [integ_eq hfin hk (hg.shift hv), integ_eq hfin hk hg]
  haveI := hfin _ hk
  letI := Fintype.ofFinite (Qt k H)
  rw [avg_eq_sum, avg_eq_sum]
  congr 1
  let m : Qt k H := QuotientAddGroup.mk (⟨v, hv⟩ : H)
  have key : ∀ q : Qt k H, g (((q.out : H) : W) + v) = g ((((q + m).out : H) : W)) := by
    intro q
    have h1 : q + m = QuotientAddGroup.mk (q.out + ⟨v, hv⟩) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [h1, hg.out_mk]
    rfl
  simp_rw [key]
  exact Fintype.sum_equiv (Equiv.addRight m) _ _ (fun q => rfl)

theorem integ_one : integ H (fun _ => (1 : ℂ)) = 1 := by
  classical
  have hinv : IsInv 1 H (fun _ => (1 : ℂ)) := fun _ _ _ _ => rfl
  rw [integ_eq hfin Nat.one_pos hinv]
  haveI := hfin _ Nat.one_pos
  letI := Fintype.ofFinite (Qt 1 H)
  rw [avg_eq_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : (Fintype.card (Qt 1 H) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact inv_mul_cancel₀ this

theorem integ_twist {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) {ζ : ℂ}
    (hζ : ζ ≠ 1) (htw : ∀ t ∈ H, g (t + v) = ζ * g t) : integ H g = 0 := by
  have h1 := integ_shift hfin hk hg hv
  rw [integ_congr hfin htw, integ_cmul hfin hk hg] at h1
  have : (ζ - 1) * integ H g = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hζ
  · exact h

theorem integ_cmul' (g : W → ℂ) (c : ℂ) : integ H (fun t => c * g t) = c * integ H g := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    have h0 : IsInv 1 H (fun _ : W => (0 : ℂ)) := fun _ _ _ _ => rfl
    rw [integ_eq hfin Nat.one_pos h0]
    simp [avg]
  by_cases hg : ∃ k, 0 < k ∧ IsInv k H g
  · obtain ⟨k, hk, hgk⟩ := hg
    exact integ_cmul hfin hk hgk c
  · have hn : ¬ ∃ k, 0 < k ∧ IsInv k H (fun t => c * g t) := by
      rintro ⟨k, hk, hgk⟩
      refine hg ⟨k, hk, ?_⟩
      refine (hgk.cmul c⁻¹).congr fun t _ => ?_
      simp [hc]
    rw [integ, dif_neg hn, integ, dif_neg hg, mul_zero]

theorem integ_zero_of {g : W → ℂ} (h : ∀ t ∈ H, g t = 0) : integ H g = 0 := by
  have h1 : integ H g = integ H (fun t => (0 : ℂ) * (fun _ => (1 : ℂ)) t) :=
    integ_congr hfin fun t ht => by simp [h t ht]
  rw [h1, integ_cmul' hfin, zero_mul]

end Integ

end Formalism.IndefR.Fin.Four

end

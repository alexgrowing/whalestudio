import Formalism.MahlerMeasure.StatementTM
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeY
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeBij
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeInto
import Mathlib

namespace Formalism.GM.DimensionMonotonicity

open Finset

def dl {r : ℕ} (a b : Fin r) : Fin r → ℤ := Pi.single a 1 - Pi.single b 1

lemma dl_self {r : ℕ} (a : Fin r) : dl a a = 0 := by
  first | (simp only [dl, sub_self]) | (unfold dl; exact sub_self _)

lemma dl_apply {r : ℕ} (a b c : Fin r) :
    dl a b c = (if c = a then 1 else 0) - (if c = b then 1 else 0) := by
  unfold dl
  rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]

lemma dl_ne_zero {r : ℕ} {a b : Fin r} (h : a ≠ b) : dl a b ≠ 0 := by
  intro h0
  have h1 := congrFun h0 a
  rw [dl_apply, if_pos rfl, if_neg h] at h1
  simp at h1

structure GlW (K : Type) (V : Type) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) where
  E : Fin r → Fin r → V →ₗ[K] V
  comm : ∀ a b c d x, E a b (E c d x) - E c d (E a b x) =
    (if b = c then E a d x else 0) - (if d = a then E c b x else 0)
  comp : (Fin r → ℤ) → V →ₗ[K] V
  dec : ∀ x, ∃ S : Finset (Fin r → ℤ), ∀ μ ∉ S, comp μ x = 0
  sum_comp : ∀ x (S : Finset (Fin r → ℤ)), (∀ μ ∉ S, comp μ x = 0) → ∑ μ ∈ S, comp μ x = x
  idem : ∀ μ ν x, comp μ (comp ν x) = if μ = ν then comp ν x else 0
  diag : ∀ c μ x, E c c (comp μ x) = ((μ c : ℤ) : K) • comp μ x
  shift : ∀ a b μ x, comp μ (E a b x) = E a b (comp (μ - dl a b) x)

namespace GlW

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

def Stable (U : Submodule K V) : Prop := ∀ a b, ∀ x ∈ U, G.E a b x ∈ U
def Graded (U : Submodule K V) : Prop := ∀ μ, ∀ x ∈ U, G.comp μ x ∈ U
def Raising (U : Submodule K V) : Prop := ∀ a b, a < b → ∀ x ∈ U, G.E a b x ∈ U
def FinW (U : Submodule K V) : Prop := ∃ S : Finset (Fin r → ℤ), ∀ x ∈ U, ∀ μ ∉ S, G.comp μ x = 0
def gS (s : Set V) : Submodule K V := sInf {U | s ⊆ U ∧ G.Stable U}
def IsWt (μ : Fin r → ℤ) (x : V) : Prop := G.comp μ x = x
def IsHW (μ : Fin r → ℤ) (x : V) : Prop := G.IsWt μ x ∧ ∀ a b, a < b → G.E a b x = 0

lemma comp_of_isWt {μ ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) :
    G.comp μ x = if μ = ν then x else 0 := by
  have h' : G.comp ν x = x := h
  calc G.comp μ x = G.comp μ (G.comp ν x) := by rw [h']
    _ = if μ = ν then x else 0 := by rw [G.idem, h']

lemma isWt_comp (μ : Fin r → ℤ) (x : V) : G.IsWt μ (G.comp μ x) := by
  show G.comp μ (G.comp μ x) = G.comp μ x
  rw [G.idem, if_pos rfl]

lemma isWt_E {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (a b : Fin r) :
    G.IsWt (ν + dl a b) (G.E a b x) := by
  show G.comp (ν + dl a b) (G.E a b x) = G.E a b x
  rw [G.shift, add_sub_cancel_right, show G.comp ν x = x from h]

lemma E_diag_of_isWt {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (c : Fin r) :
    G.E c c x = ((ν c : ℤ) : K) • x := by
  have h' : G.comp ν x = x := h
  have h2 := G.diag c ν x
  rwa [h'] at h2

lemma comp_Ecc (μ : Fin r → ℤ) (c : Fin r) (x : V) :
    G.comp μ (G.E c c x) = ((μ c : ℤ) : K) • G.comp μ x := by
  rw [G.shift, dl_self, sub_zero, G.diag]

lemma sum_comp_eq (x : V) {S : Finset (Fin r → ℤ)} (h : ∀ μ ∉ S, G.comp μ x = 0) :
    x = ∑ μ ∈ S, G.comp μ x := (G.sum_comp x S h).symm

theorem weight_component_mem_submodule [CharZero K] (U : Submodule K V) (hU : ∀ c, ∀ x ∈ U, G.E c c x ∈ U) :
    ∀ (S : Finset (Fin r → ℤ)) (x : V), x ∈ U → (∀ μ ∉ S, G.comp μ x = 0) → ∀ μ, G.comp μ x ∈ U := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro x hx hS μ
  by_cases hsub : ∃ ν ∈ S, ∃ ν' ∈ S, ν ≠ ν'
  · obtain ⟨ν, hν, ν', hν', hne⟩ := hsub
    obtain ⟨c, hc⟩ : ∃ c, ν c ≠ ν' c := by
      by_contra hcon
      push_neg at hcon
      exact hne (funext hcon)
    have key : ∀ κ ∈ S, μ c ≠ κ c → G.comp μ x ∈ U := by
      intro κ hκ hμκ
      have hyU : G.E c c x - ((κ c : ℤ) : K) • x ∈ U := U.sub_mem (hU c x hx) (U.smul_mem _ hx)
      have hcy : ∀ ρ, G.comp ρ (G.E c c x - ((κ c : ℤ) : K) • x) =
          (((ρ c : ℤ) : K) - ((κ c : ℤ) : K)) • G.comp ρ x := by
        intro ρ
        rw [map_sub, map_smul, G.comp_Ecc, sub_smul]
      have hyS : ∀ ρ ∉ S.erase κ, G.comp ρ (G.E c c x - ((κ c : ℤ) : K) • x) = 0 := by
        intro ρ hρ
        rw [hcy]
        by_cases hρκ : ρ = κ
        · rw [hρκ, sub_self, zero_smul]
        · have hρS : ρ ∉ S := fun h' => hρ (Finset.mem_erase.mpr ⟨hρκ, h'⟩)
          rw [hS ρ hρS, smul_zero]
      have h1 := ih (S.erase κ) (Finset.erase_ssubset hκ) _ hyU hyS μ
      rw [hcy] at h1
      have hne' : (((μ c : ℤ) : K) - ((κ c : ℤ) : K)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hμκ
      have h2 := U.smul_mem ((((μ c : ℤ) : K) - ((κ c : ℤ) : K))⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at h2
    by_cases h1 : μ c = ν c
    · exact key ν' hν' (by rw [h1]; exact hc)
    · exact key ν hν h1
  · push_neg at hsub
    by_cases hμ : μ ∈ S
    · have hsing : ∀ ρ ∉ ({μ} : Finset (Fin r → ℤ)), G.comp ρ x = 0 := by
        intro ρ hρ
        apply hS
        intro hρS
        exact hρ (Finset.mem_singleton.mpr (hsub ρ hρS μ hμ))
      have h2 := G.sum_comp x {μ} hsing
      rw [Finset.sum_singleton] at h2
      rw [h2]
      exact hx
    · rw [hS μ hμ]
      exact U.zero_mem

theorem graded_of [CharZero K] {U : Submodule K V} (hU : G.Stable U) : G.Graded U := by
  intro μ x hx
  obtain ⟨S, hS⟩ := G.dec x
  exact G.weight_component_mem_submodule U (fun c y hy => hU c c y hy) S x hx hS μ

lemma raising_of {U : Submodule K V} (hU : G.Stable U) : G.Raising U := fun a b _ x hx => hU a b x hx

lemma gS_stable (s : Set V) : G.Stable (G.gS s) := by
  intro a b x hx
  exact Submodule.mem_sInf.mpr fun U hU => hU.2 a b x (Submodule.mem_sInf.mp hx U hU)

lemma subset_gS (s : Set V) : s ⊆ G.gS s := by
  intro x hx
  exact Submodule.mem_sInf.mpr fun U hU => hU.1 hx

lemma gS_le {s : Set V} {U : Submodule K V} (hs : s ⊆ U) (hU : G.Stable U) : G.gS s ≤ U := by
  apply sInf_le
  exact ⟨hs, hU⟩

def Cas : V →ₗ[K] V := ∑ a, ∑ b, G.E a b ∘ₗ G.E b a

lemma Cas_apply (x : V) : G.Cas x = ∑ a, ∑ b, G.E a b (G.E b a x) := by
  simp only [Cas, LinearMap.sum_apply, LinearMap.comp_apply]

lemma comm' (a b c d : Fin r) (x : V) : G.E a b (G.E c d x) = G.E c d (G.E a b x) +
    ((if b = c then G.E a d x else 0) - (if d = a then G.E c b x else 0)) := by
  rw [← G.comm a b c d x]
  abel

theorem E_Cas (c d : Fin r) (x : V) : G.E c d (G.Cas x) = G.Cas (G.E c d x) := by
  have key : ∀ a b, G.E c d (G.E a b (G.E b a x)) = G.E a b (G.E b a (G.E c d x)) +
      (((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) -
        ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0))) := by
    intro a b
    rw [G.comm' c d a b, G.comm' c d b a x, map_add, map_sub]
    split_ifs <;> subst_vars <;> (try simp only [map_zero]) <;> abel
  have h1 : ∀ a, ∑ b, ((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) = 0 := by
    intro a
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  have h2 : ∑ a, ∑ b, ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  calc G.E c d (G.Cas x) = ∑ a, ∑ b, G.E c d (G.E a b (G.E b a x)) := by
        rw [Cas_apply, map_sum]
        simp only [map_sum]
    _ = ∑ a, ∑ b, (G.E a b (G.E b a (G.E c d x)) +
        (((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) -
          ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0)))) := by
        simp only [key]
    _ = G.Cas (G.E c d x) + (∑ a, ∑ b, ((if d = b then G.E a d (G.E c a x) else 0) - (if b = c then G.E a d (G.E c a x) else 0)) -
        ∑ a, ∑ b, ((if a = c then G.E c b (G.E b d x) else 0) - (if d = a then G.E c b (G.E b d x) else 0))) := by
        rw [Cas_apply]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = G.Cas (G.E c d x) := by
        rw [h2, Finset.sum_eq_zero (fun a _ => h1 a), sub_zero, add_zero]

lemma Cas_mem {U : Submodule K V} (hU : G.Stable U) {x : V} (hx : x ∈ U) : G.Cas x ∈ U := by
  rw [Cas_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hU a b _ (hU b a x hx)

lemma comp_Cas (μ : Fin r → ℤ) (x : V) : G.comp μ (G.Cas x) = G.Cas (G.comp μ x) := by
  rw [Cas_apply, Cas_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : μ - dl a b - dl b a = μ := by
    funext c
    simp only [Pi.sub_apply, dl_apply]
    split_ifs <;> omega
  rw [G.shift, G.shift, e]

def casI (μ : Fin r → ℤ) : ℤ :=
  ∑ a, ∑ b, (if a = b then μ a * μ a else if a < b then μ a - μ b else 0)

theorem Cas_hwmod {U : Submodule K V} (hU : G.Stable U) {μ : Fin r → ℤ} {v : V} (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : G.Cas v - ((casI μ : ℤ) : K) • v ∈ U := by
  have hmem : ∀ a b, G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v ∈ U := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [if_neg h.ne, if_pos h, G.comm' a b b a v, if_pos rfl, if_pos rfl,
        G.E_diag_of_isWt hv a, G.E_diag_of_isWt hv b]
      have hm : G.E b a (G.E a b v) ∈ U := hU b a _ (hr a b h)
      convert hm using 1
      push_cast
      rw [sub_smul]
      abel
    · subst h
      rw [if_pos rfl, G.E_diag_of_isWt hv a, map_smul, G.E_diag_of_isWt hv a, smul_smul]
      simp
    · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), Int.cast_zero, zero_smul, sub_zero]
      exact hU a b _ (hr b a h)
  have hsum : G.Cas v - ((casI μ : ℤ) : K) • v = ∑ a, ∑ b, (G.E a b (G.E b a v) -
      (((if a = b then μ a * μ a else if a < b then μ a - μ b else 0 : ℤ)) : K) • v) := by
    rw [Cas_apply, casI, Int.cast_sum, Finset.sum_smul]
    simp only [Int.cast_sum, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hmem a b

end GlW

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open Finset

def psum {r : ℕ} (μ : Fin r → ℤ) (k : ℕ) : ℤ := ∑ c : Fin r, if (c : ℕ) < k then μ c else 0

def Dle {r : ℕ} (μ ν : Fin r → ℤ) : Prop := (∀ k, psum μ k ≤ psum ν k) ∧ ∑ c, μ c = ∑ c, ν c

def DomW {r : ℕ} (μ : Fin r → ℤ) : Prop := ∀ a b : Fin r, a < b → μ b ≤ μ a

variable {r : ℕ}

lemma psum_add (μ ν : Fin r → ℤ) (k : ℕ) : psum (μ + ν) k = psum μ k + psum ν k := by
  unfold psum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

lemma psum_sub (μ ν : Fin r → ℤ) (k : ℕ) : psum (μ - ν) k = psum μ k - psum ν k := by
  unfold psum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

lemma Dle_refl (μ : Fin r → ℤ) : Dle μ μ := ⟨fun _ => le_rfl, rfl⟩

lemma Dle_trans {μ ν κ : Fin r → ℤ} (h1 : Dle μ ν) (h2 : Dle ν κ) : Dle μ κ := ⟨fun k => (h1.1 k).trans (h2.1 k), h1.2.trans h2.2⟩

lemma psum_succ_sub (μ : Fin r → ℤ) (c : Fin r) : psum μ (c + 1) - psum μ c = μ c := by
  unfold psum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    have hbc : (b : ℕ) ≠ c := fun h' => hb (Fin.ext h')
    split_ifs <;> omega
  · intro h'
    exact absurd (Finset.mem_univ c) h'

lemma Dle_antisymm {μ ν : Fin r → ℤ} (h1 : Dle μ ν) (h2 : Dle ν μ) : μ = ν := by
  funext c
  have e : ∀ k, psum μ k = psum ν k := fun k => le_antisymm (h1.1 k) (h2.1 k)
  rw [← psum_succ_sub μ c, ← psum_succ_sub ν c, e, e]

lemma psum_dl (a b : Fin r) (k : ℕ) :
    psum (dl a b) k = (if (a : ℕ) < k then 1 else 0) - (if (b : ℕ) < k then 1 else 0) := by
  have hs : ∀ e : Fin r, psum (Pi.single e (1 : ℤ)) k = if (e : ℕ) < k then 1 else 0 := by
    intro e
    unfold psum
    rw [Finset.sum_eq_single e]
    · simp
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · intro h'
      exact absurd (Finset.mem_univ e) h'
  rw [dl, psum_sub, hs, hs]

lemma sum_dl (a b : Fin r) : ∑ c, dl a b c = 0 := by
  first
    | (simp [dl_apply, Finset.sum_sub_distrib])
    | (unfold dl
       simp only [Pi.sub_apply, Finset.sum_sub_distrib]
       rw [Finset.sum_pi_single', Finset.sum_pi_single']
       simp)

lemma Dle_add_right {μ ν : Fin r → ℤ} (h : Dle μ ν) (κ : Fin r → ℤ) : Dle (μ + κ) (ν + κ) := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [psum_add, psum_add]
    linarith [h.1 k]
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h.2]

lemma Dle_lower (ν : Fin r → ℤ) {a b : Fin r} (hab : b < a) : Dle (ν + dl a b) ν := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [psum_add, psum_dl]
    have hba : (b : ℕ) < a := hab
    split_ifs <;> omega
  · simp only [Pi.add_apply, Finset.sum_add_distrib, sum_dl, add_zero]

lemma Dle_raise (ν : Fin r → ℤ) {a b : Fin r} (hab : a < b) : Dle ν (ν + dl a b) := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [psum_add, psum_dl]
    have hab' : (a : ℕ) < b := hab
    split_ifs <;> omega
  · simp only [Pi.add_apply, Finset.sum_add_distrib, sum_dl, add_zero]

lemma psum_range (g : ℕ → ℤ) {k r : ℕ} (h : k ≤ r) :
    ∑ c ∈ range r, (if c < k then g c else 0) = ∑ c ∈ range k, g c := by
  rw [← Finset.sum_filter]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h'
    exact h'.2
  · intro h'
    exact ⟨by omega, h'⟩

theorem abel_ineq (r : ℕ) (δ t : ℕ → ℤ) (hD : ∀ k ≤ r, 0 ≤ ∑ c ∈ range k, δ c)
    (hT : ∑ c ∈ range r, δ c = 0) (ht : ∀ c, c + 1 < r → 2 ≤ t c - t (c + 1)) :
    0 ≤ ∑ c ∈ range r, t c * δ c ∧ (∑ c ∈ range r, t c * δ c = 0 → ∀ c < r, δ c = 0) := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℤ, ∀ k, D k = ∑ i ∈ range k, δ i := ⟨_, fun k => rfl⟩
  have hD0 : D 0 = 0 := by rw [hDdef]; simp
  have hDs : ∀ k, D (k + 1) = D k + δ k := fun k => by rw [hDdef, hDdef, Finset.sum_range_succ]
  have hDnn : ∀ k ≤ r, 0 ≤ D k := fun k hk => by rw [hDdef]; exact hD k hk
  have hDr : D r = 0 := by rw [hDdef]; exact hT
  have hid : ∀ n, ∑ c ∈ range n, t c * δ c =
      ∑ c ∈ range n, (t c - t (c + 1)) * D (c + 1) + t n * D n := by
    intro n
    induction n with
    | zero => simp [hD0]
    | succ n ih =>
      rw [Finset.sum_range_succ (fun c => t c * δ c), ih,
        Finset.sum_range_succ (fun c => (t c - t (c + 1)) * D (c + 1)), hDs n]
      ring
  have hterm : ∀ c ∈ range r, 0 ≤ (t c - t (c + 1)) * D (c + 1) := by
    intro c hc
    rw [Finset.mem_range] at hc
    by_cases hcr : c + 1 < r
    · exact mul_nonneg (by linarith [ht c hcr]) (hDnn (c + 1) (by omega))
    · have hc1 : c + 1 = r := by omega
      rw [hc1, hDr, mul_zero]
  rw [hid r, hDr, mul_zero, add_zero]
  refine ⟨Finset.sum_nonneg hterm, fun h0 c hc => ?_⟩
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0
  have hDz : ∀ k, k ≤ r → D k = 0 := by
    intro k hk
    rcases k with _ | c'
    · exact hD0
    · by_cases hcr : c' + 1 < r
      · have h1 := hall c' (Finset.mem_range.mpr (by omega))
        have h2 := ht c' hcr
        rcases mul_eq_zero.mp h1 with h3 | h3
        · omega
        · exact h3
      · have hc1 : c' + 1 = r := by omega
        rw [hc1, hDr]
  have h5 := hDs c
  rw [hDz (c + 1) (by omega), hDz c (by omega)] at h5
  linarith

lemma casI_closed (μ : Fin r → ℤ) : GlW.casI μ = ∑ c : Fin r, μ c * (μ c + ((r : ℤ) - 1 - 2 * (c : ℤ))) := by
  unfold GlW.casI
  have hsplit : ∀ a b : Fin r, (if a = b then μ a * μ a else if a < b then μ a - μ b else 0) =
      (if a = b then μ a * μ a else 0) + ((if a < b then μ a else 0) - (if a < b then μ b else 0)) := by
    intro a b
    split_ifs <;> first | (exfalso; subst_vars; exact lt_irrefl _ ‹_›) | ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if a < b then μ b else 0)]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio,
    Fin.card_Ioi, Fin.card_Iio]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc := c.isLt
  rw [Nat.cast_sub (show (c : ℕ) ≤ r - 1 by omega), Nat.cast_sub (show 1 ≤ r by omega)]
  push_cast
  ring

theorem cas_lt {μ ν : Fin r → ℤ} (hμ : DomW μ) (hν : DomW ν) (h : Dle μ ν) (hne : μ ≠ ν) :
    GlW.casI μ < GlW.casI ν := by
  obtain ⟨E, hE⟩ : ∃ E : (Fin r → ℤ) → ℕ → ℤ, ∀ κ k (h : k < r), E κ k = κ ⟨k, h⟩ :=
    ⟨fun κ k => if h : k < r then κ ⟨k, h⟩ else 0, fun κ k h => dif_pos h⟩
  have hsumE : ∀ κ : Fin r → ℤ, ∑ c : Fin r, κ c = ∑ k ∈ range r, E κ k := by
    intro κ
    rw [← Fin.sum_univ_eq_sum_range (E κ) r]
    exact Finset.sum_congr rfl fun c _ => (hE κ c c.isLt).symm
  have hpsum : ∀ (κ : Fin r → ℤ) k, k ≤ r → psum κ k = ∑ j ∈ range k, E κ j := by
    intro κ k hk
    unfold psum
    rw [hsumE (fun c => if (c : ℕ) < k then κ c else 0), ← psum_range (E κ) hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [hE _ j hj, Fin.val_mk]
  have hS : GlW.casI ν - GlW.casI μ =
      ∑ k ∈ range r, (E ν k + E μ k + ((r : ℤ) - 1 - 2 * k)) * (E ν k - E μ k) := by
    rw [casI_closed ν, casI_closed μ, ← Finset.sum_sub_distrib,
      hsumE (fun c => ν c * (ν c + ((r : ℤ) - 1 - 2 * (c : ℤ))) - μ c * (μ c + ((r : ℤ) - 1 - 2 * (c : ℤ))))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    simp only [hE _ k hk, Fin.val_mk]
    ring
  have hab := abel_ineq r (fun k => E ν k - E μ k) (fun k => E ν k + E μ k + ((r : ℤ) - 1 - 2 * k))
    (fun k hk => by
      show 0 ≤ ∑ c ∈ range k, (E ν c - E μ c)
      rw [Finset.sum_sub_distrib, ← hpsum ν k hk, ← hpsum μ k hk]
      linarith [h.1 k])
    (by
      show ∑ c ∈ range r, (E ν c - E μ c) = 0
      rw [Finset.sum_sub_distrib, ← hsumE ν, ← hsumE μ, h.2, sub_self])
    (fun c hc => by
      show 2 ≤ (E ν c + E μ c + ((r : ℤ) - 1 - 2 * ((c : ℕ) : ℤ))) -
        (E ν (c + 1) + E μ (c + 1) + ((r : ℤ) - 1 - 2 * ((c + 1 : ℕ) : ℤ)))
      have h1 := hμ ⟨c, by omega⟩ ⟨c + 1, hc⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self c))
      have h2 := hν ⟨c, by omega⟩ ⟨c + 1, hc⟩ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self c))
      rw [hE ν c (by omega), hE μ c (by omega), hE ν (c + 1) hc, hE μ (c + 1) hc]
      push_cast
      linarith)
  have h0 : (0 : ℤ) ≤ ∑ k ∈ range r, (E ν k + E μ k + ((r : ℤ) - 1 - 2 * k)) * (E ν k - E μ k) := hab.1
  have hne0 : ∑ k ∈ range r, (E ν k + E μ k + ((r : ℤ) - 1 - 2 * k)) * (E ν k - E μ k) ≠ 0 := by
    intro hz
    apply hne
    funext c
    have h3 : E ν c - E μ c = 0 := hab.2 hz c c.isLt
    rw [hE ν c c.isLt, hE μ c c.isLt] at h3
    simp only [Fin.eta] at h3
    linarith
  rw [← hS] at h0 hne0
  omega

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open Finset

namespace GlW

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

lemma isWt_pow {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (a b : Fin r) (k : ℕ) :
    G.IsWt (ν + (k : ℤ) • dl a b) ((G.E a b ^ k) x) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hE : (G.E a b ^ (k + 1)) x = G.E a b ((G.E a b ^ k) x) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hE]
    have h2 := G.isWt_E ih a b
    have e : ν + ((k + 1 : ℕ) : ℤ) • dl a b = ν + (k : ℤ) • dl a b + dl a b := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e]
    exact h2

lemma pow_mem {U : Submodule K V} (hU : G.Stable U) (a b : Fin r) (k : ℕ) {x : V} (hx : x ∈ U) :
    (G.E a b ^ k) x ∈ U := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hU a b _ ih

theorem sl2 {a b : Fin r} (hab : a ≠ b) {ν : Fin r → ℤ} {x : V} (hx : G.IsWt ν x) (k : ℕ) :
    G.E a b ((G.E b a ^ (k + 1)) x) = (G.E b a ^ (k + 1)) (G.E a b x) +
      (((k + 1 : ℕ) : K) * ((ν a - ν b - k : ℤ) : K)) • (G.E b a ^ k) x := by
  have hcomm : ∀ y, G.E a b (G.E b a y) = G.E b a (G.E a b y) + (G.E a a y - G.E b b y) := by
    intro y
    rw [G.comm' a b b a y, if_pos rfl, if_pos rfl]
  have hp : ∀ (j : ℕ) (y : V), G.E b a ((G.E b a ^ j) y) = (G.E b a ^ (j + 1)) y := by
    intro j y
    rw [pow_succ', Module.End.mul_apply]
  have hdiag : ∀ j : ℕ, G.E a a ((G.E b a ^ j) x) - G.E b b ((G.E b a ^ j) x) =
      ((ν a - ν b - 2 * (j : ℤ) : ℤ) : K) • (G.E b a ^ j) x := by
    intro j
    have hw := G.isWt_pow hx b a j
    rw [G.E_diag_of_isWt hw a, G.E_diag_of_isWt hw b, ← sub_smul]
    have e1 : (ν + (j : ℤ) • dl b a) a = ν a - j := by
      rw [Pi.add_apply, Pi.smul_apply, dl_apply, if_neg hab, if_pos rfl, smul_eq_mul]
      ring
    have e2 : (ν + (j : ℤ) • dl b a) b = ν b + j := by
      rw [Pi.add_apply, Pi.smul_apply, dl_apply, if_pos rfl, if_neg (Ne.symm hab), smul_eq_mul]
      ring
    rw [e1, e2]
    push_cast
    ring_nf
  induction k with
  | zero =>
    have h0 := hdiag 0
    simp only [pow_zero, Module.End.one_apply] at h0
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply]
    rw [hcomm, h0]
    congr 2
    push_cast
    ring
  | succ k ih =>
    rw [← hp (k + 1) x, ← hp (k + 1) (G.E a b x), hcomm, ih, hdiag (k + 1), map_add, map_smul, hp k x,
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem dom_of_hwmod {U W : Submodule K V} (hU : G.Stable U) (hW : G.Stable W) (hWf : G.FinW W)
    {μ : Fin r → ℤ} {v : V} (hvW : v ∈ W) (hvU : v ∉ U) (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : DomW μ := by
  intro a b hab
  by_contra hlt
  push_neg at hlt
  have hne : a ≠ b := hab.ne
  have key : ∀ k : ℕ, (G.E b a ^ k) v ∉ U := by
    intro k
    induction k with
    | zero => simpa using hvU
    | succ k ih =>
      intro hk
      apply ih
      have h1 := hU a b _ hk
      rw [G.sl2 hne hv k] at h1
      have h2 : (G.E b a ^ (k + 1)) (G.E a b v) ∈ U := G.pow_mem hU b a (k + 1) (hr a b hab)
      have h3 := U.sub_mem h1 h2
      rw [add_sub_cancel_left] at h3
      have hc : (((k + 1 : ℕ) : K) * ((μ a - μ b - k : ℤ) : K)) ≠ 0 := by
        apply mul_ne_zero
        · first
            | exact_mod_cast Nat.succ_ne_zero k
            | exact Nat.cast_add_one_ne_zero k
            | (push_cast; exact Nat.cast_add_one_ne_zero k)
        · have h6 : μ a - μ b - (k : ℤ) ≠ 0 := by omega
          exact_mod_cast h6
      have h4 := U.smul_mem (((k + 1 : ℕ) : K) * ((μ a - μ b - k : ℤ) : K))⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h4
  obtain ⟨S, hS⟩ := hWf
  have hinj : Function.Injective (fun k : ℕ => μ + (k : ℤ) • dl b a) := by
    intro k l hkl
    have h7 := congrFun hkl a
    simp [dl_apply, hne] at h7
    omega
  have hex : ∃ w ∈ Set.range (fun k : ℕ => μ + (k : ℤ) • dl b a), w ∉ S := by
    first
      | exact (Set.infinite_range_of_injective hinj).exists_not_mem_finset S
      | exact (Set.infinite_range_of_injective hinj).exists_notMem_finset S
  obtain ⟨w, ⟨k, rfl⟩, hw⟩ := hex
  have hwt' : G.comp (μ + (k : ℤ) • dl b a) ((G.E b a ^ k) v) = (G.E b a ^ k) v := G.isWt_pow hv b a k
  have hkW : (G.E b a ^ k) v ∈ W := G.pow_mem hW b a k hvW
  have h0 : (G.E b a ^ k) v = 0 := hwt'.symm.trans (hS _ hkW _ hw)
  exact key k (by rw [h0]; exact U.zero_mem)

def Low (la : Fin r → ℤ) : Submodule K V where
  carrier := {x | ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν x = 0}
  add_mem' := by
    intro x y hx hy ν hν
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx ν hν, hy ν hν, add_zero]
  zero_mem' := by intro ν _; simp
  smul_mem' := by
    intro c x hx ν hν
    simp only [Set.mem_ofPred_eq] at hx
    rw [map_smul, hx ν hν, smul_zero]

def Lw (v : V) : Submodule K V := sInf {U | v ∈ U ∧ ∀ a b, b < a → ∀ x ∈ U, G.E a b x ∈ U}

lemma mem_Lw (v : V) : v ∈ G.Lw v := by
  exact Submodule.mem_sInf.mpr fun U hU => hU.1

lemma Lw_lower (v : V) {a b : Fin r} (h : b < a) {x : V} (hx : x ∈ G.Lw v) : G.E a b x ∈ G.Lw v := by
  exact Submodule.mem_sInf.mpr fun U hU => hU.2 a b h x (Submodule.mem_sInf.mp hx U hU)

lemma Lw_le (v : V) {U : Submodule K V} (hv : v ∈ U) (hU : ∀ a b, b < a → ∀ x ∈ U, G.E a b x ∈ U) :
    G.Lw v ≤ U := by
  apply sInf_le
  exact ⟨hv, hU⟩

theorem Lw_stable {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) : G.Stable (G.Lw v) := by
  let U' : Submodule K V :=
    { carrier := {x | x ∈ G.Lw v ∧ ∀ a b, G.E a b x ∈ G.Lw v}
      add_mem' := fun {x y} hx hy => ⟨(G.Lw v).add_mem hx.1 hy.1, fun a b => by
        rw [map_add]; exact (G.Lw v).add_mem (hx.2 a b) (hy.2 a b)⟩
      zero_mem' := ⟨(G.Lw v).zero_mem, fun a b => by rw [map_zero]; exact (G.Lw v).zero_mem⟩
      smul_mem' := fun c x hx => ⟨(G.Lw v).smul_mem c hx.1, fun a b => by
        rw [map_smul]; exact (G.Lw v).smul_mem c (hx.2 a b)⟩ }
  have hle : G.Lw v ≤ U' := by
    apply G.Lw_le
    · show v ∈ G.Lw v ∧ ∀ a b, G.E a b v ∈ G.Lw v
      refine ⟨G.mem_Lw v, fun a b => ?_⟩
      rcases lt_trichotomy a b with h | h | h
      · rw [hv.2 a b h]; exact (G.Lw v).zero_mem
      · subst h; rw [G.E_diag_of_isWt hv.1]; exact (G.Lw v).smul_mem _ (G.mem_Lw v)
      · exact G.Lw_lower v h (G.mem_Lw v)
    · intro c d hcd x hx
      have hx' : x ∈ G.Lw v ∧ ∀ a b, G.E a b x ∈ G.Lw v := hx
      show G.E c d x ∈ G.Lw v ∧ ∀ a b, G.E a b (G.E c d x) ∈ G.Lw v
      refine ⟨G.Lw_lower v hcd hx'.1, fun a b => ?_⟩
      rw [G.comm' a b c d x]
      refine (G.Lw v).add_mem (G.Lw_lower v hcd (hx'.2 a b)) ((G.Lw v).sub_mem ?_ ?_)
      · split_ifs
        · exact hx'.2 a d
        · exact (G.Lw v).zero_mem
      · split_ifs
        · exact hx'.2 c b
        · exact (G.Lw v).zero_mem
  intro a b x hx
  exact (show x ∈ G.Lw v ∧ ∀ a b, G.E a b x ∈ G.Lw v from hle hx).2 a b

lemma gS_le_Lw {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) : G.gS {v} ≤ G.Lw v := G.gS_le (Set.singleton_subset_iff.mpr (G.mem_Lw v)) (G.Lw_stable hv)

theorem Lw_le_low {la : Fin r → ℤ} {v : V} (hv : G.IsWt la v) :
    G.Lw v ≤ Submodule.span K {v} ⊔ G.Low la := by
  apply G.Lw_le
  · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  · intro a b hab x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, map_smul]
    apply Submodule.mem_sup_right
    refine (G.Low la).add_mem ((G.Low la).smul_mem c ?_) ?_
    · show ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν (G.E a b v) = 0
      intro ν hν
      rw [G.comp_of_isWt (G.isWt_E hv a b), if_neg]
      rintro rfl
      exact hν ⟨Dle_lower la hab, fun h => dl_ne_zero hab.ne' (by simpa using h)⟩
    · have hz' : ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν z = 0 := hz
      show ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν (G.E a b z) = 0
      intro ν hν
      rw [G.shift]
      by_cases h : Dle (ν - dl a b) la ∧ ν - dl a b ≠ la
      · exfalso
        apply hν
        have hd : Dle ν (ν - dl a b) := by
          have h5 := Dle_lower (ν - dl a b) hab
          rwa [sub_add_cancel] at h5
        refine ⟨Dle_trans hd h.1, fun heq => ?_⟩
        subst heq
        exact h.2 (Dle_antisymm hd h.1).symm
      · rw [hz' _ h, map_zero]

theorem wt_le_of_mem {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {x : V} (hx : x ∈ G.gS {v})
    {ν : Fin r → ℤ} (h : G.comp ν x ≠ 0) : Dle ν la := by
  have hx' : x ∈ Submodule.span K {v} ⊔ G.Low la := G.Lw_le_low hv.1 (G.gS_le_Lw hv hx)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  by_contra hle
  apply h
  have hz' : ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν z = 0 := hz
  have hne : ν ≠ la := fun e => hle (by rw [e]; exact Dle_refl la)
  rw [map_add, map_smul, G.comp_of_isWt hv.1, if_neg hne, smul_zero, zero_add]
  exact hz' ν (fun h' => hle h'.1)

theorem comp_top_of_mem {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {x : V} (hx : x ∈ G.gS {v}) :
    ∃ c : K, G.comp la x = c • v := by
  have hx' : x ∈ Submodule.span K {v} ⊔ G.Low la := G.Lw_le_low hv.1 (G.gS_le_Lw hv hx)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hz' : ∀ ν, ¬ (Dle ν la ∧ ν ≠ la) → G.comp ν z = 0 := hz
  refine ⟨c, ?_⟩
  rw [map_add, map_smul, show G.comp la v = v from hv.1, hz' la (fun h => h.2 rfl), add_zero]

theorem Cas_gS {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {x : V} (hx : x ∈ G.gS {v}) :
    G.Cas x = ((casI la : ℤ) : K) • x := by
  have hvU : G.Cas v - ((casI la : ℤ) : K) • v = 0 := by
    have h0 := G.Cas_hwmod (fun a b y hy => by rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero]) hv.1 (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)
    rwa [Submodule.mem_bot] at h0
  let U : Submodule K V := LinearMap.ker (G.Cas - ((casI la : ℤ) : K) • LinearMap.id)
  have hmem : ∀ y, y ∈ U ↔ G.Cas y - ((casI la : ℤ) : K) • y = 0 := fun y => by
    first
      | simp only [U, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      | simp [U]
  have hstab : G.Stable U := by
    intro a b y hy
    rw [hmem] at hy ⊢
    rw [← G.E_Cas, ← map_smul, ← map_sub, hy, map_zero]
  have hle := G.gS_le (Set.singleton_subset_iff.mpr ((hmem v).mpr hvU)) hstab
  exact sub_eq_zero.mp ((hmem x).mp (hle hx))

lemma bot_stable : G.Stable (⊥ : Submodule K V) := by
  intro a b x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

theorem hw_in_gS {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {W : Submodule K V} (hW : G.Stable W)
    (hWf : G.FinW W) (hvW : v ∈ W) {x : V} (hx : x ∈ G.gS {v}) {μ : Fin r → ℤ} (hxw : G.IsHW μ x)
    (hx0 : x ≠ 0) : μ = la ∧ ∃ c : K, x = c • v := by
  have hx1 : G.comp μ x = x := hxw.1
  have hdle : Dle μ la := G.wt_le_of_mem hv hx (by rw [hx1]; exact hx0)
  by_cases hμ : μ = la
  · subst hμ
    refine ⟨rfl, ?_⟩
    obtain ⟨c, hc⟩ := G.comp_top_of_mem hv hx
    exact ⟨c, by rw [← hc, hx1]⟩
  · exfalso
    have hv0 : v ≠ 0 := by
      rintro rfl
      apply hx0
      have h8 : G.gS {(0 : V)} ≤ ⊥ :=
        G.gS_le (Set.singleton_subset_iff.mpr (Submodule.zero_mem _)) G.bot_stable
      exact (Submodule.mem_bot K).mp (h8 hx)
    have hxW : x ∈ W := G.gS_le (Set.singleton_subset_iff.mpr hvW) hW hx
    have hdomla : DomW la := G.dom_of_hwmod G.bot_stable hW hWf hvW (by rwa [Submodule.mem_bot]) hv.1
      (fun a b h => by rw [hv.2 a b h]; exact Submodule.zero_mem _)
    have hdomμ : DomW μ := G.dom_of_hwmod G.bot_stable hW hWf hxW (by rwa [Submodule.mem_bot]) hxw.1
      (fun a b h => by rw [hxw.2 a b h]; exact Submodule.zero_mem _)
    have hlt := cas_lt hdomμ hdomla hdle hμ
    have h1 := G.Cas_gS hv hx
    have h2 : G.Cas x = ((casI μ : ℤ) : K) • x := by
      have h0 := G.Cas_hwmod G.bot_stable hxw.1 (fun a b h => by rw [hxw.2 a b h]; exact Submodule.zero_mem _)
      rw [Submodule.mem_bot] at h0
      exact sub_eq_zero.mp h0
    rw [h1] at h2
    have h3 : (((casI la : ℤ) : K) - ((casI μ : ℤ) : K)) • x = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · rw [sub_eq_zero] at h4
      have h9 : casI la = casI μ := by exact_mod_cast h4
      omega
    · exact hx0 h4

end GlW

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open Finset

namespace GlW

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

def ht (μ : Fin r → ℤ) : ℤ := ∑ c : Fin r, (-(c : ℤ)) * μ c

lemma ht_add_dl (μ : Fin r → ℤ) (a b : Fin r) : ht (μ + dl a b) = ht μ + ((b : ℤ) - a) := by
  unfold ht
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, dl_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem exists_hwmod {W U : Submodule K V} (hWg : G.Graded W) (hWr : G.Raising W) (hWf : G.FinW W)
    (h : ¬ W ≤ U) : ∃ v ∈ W, v ∉ U ∧ ∃ μ, G.IsWt μ v ∧ ∀ a b, a < b → G.E a b v ∈ U := by
  classical
  obtain ⟨S, hS⟩ := hWf
  obtain ⟨x, hxW, hxU⟩ := SetLike.not_le_iff_exists.mp h
  have hex : ∃ μ, G.comp μ x ∉ U := by
    by_contra hcon
    push_neg at hcon
    apply hxU
    rw [G.sum_comp_eq x (fun μ hμ => hS x hxW μ hμ)]
    exact Submodule.sum_mem _ fun μ _ => hcon μ
  obtain ⟨μ0, hμ0⟩ := hex
  have hμ0S : μ0 ∈ S := by
    by_contra hn
    exact hμ0 (by rw [hS x hxW μ0 hn]; exact U.zero_mem)
  have hTne : (S.filter (fun μ => ∃ v ∈ W, v ∉ U ∧ G.IsWt μ v)).Nonempty :=
    ⟨μ0, Finset.mem_filter.mpr ⟨hμ0S, G.comp μ0 x, hWg μ0 x hxW, hμ0, G.isWt_comp μ0 x⟩⟩
  obtain ⟨μ, hμT, hmax⟩ := Finset.exists_max_image _ ht hTne
  obtain ⟨_, v, hvW, hvU, hv⟩ := Finset.mem_filter.mp hμT
  refine ⟨v, hvW, hvU, μ, hv, fun a b hab => ?_⟩
  by_contra hE
  have hw := G.isWt_E hv a b
  have hWE : G.E a b v ∈ W := hWr a b hab v hvW
  have hS' : μ + dl a b ∈ S := by
    by_contra hn
    apply hE
    have h0 : G.E a b v = 0 :=
      (show G.comp (μ + dl a b) (G.E a b v) = G.E a b v from hw).symm.trans (hS _ hWE _ hn)
    rw [h0]
    exact U.zero_mem
  have hle := hmax (μ + dl a b) (Finset.mem_filter.mpr ⟨hS', G.E a b v, hWE, hE, hw⟩)
  rw [ht_add_dl] at hle
  have hab' : (a : ℕ) < b := hab
  omega

def cprod : List ℤ → V →ₗ[K] V
  | [] => LinearMap.id
  | c :: cs => (G.Cas - ((c : ℤ) : K) • LinearMap.id) ∘ₗ cprod cs

lemma cprod_cons (c : ℤ) (cs : List ℤ) (x : V) :
    G.cprod (c :: cs) x = G.Cas (G.cprod cs x) - ((c : ℤ) : K) • G.cprod cs x := by
  first
    | rfl
    | simp only [cprod, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

lemma cprod_mem {U : Submodule K V} (hU : G.Stable U) (cs : List ℤ) {x : V} (hx : x ∈ U) :
    G.cprod cs x ∈ U := by
  induction cs with
  | nil => exact hx
  | cons c cs ih =>
    rw [cprod_cons]
    exact U.sub_mem (G.Cas_mem hU ih) (U.smul_mem _ ih)

lemma E_cprod (a b : Fin r) (cs : List ℤ) (x : V) : G.E a b (G.cprod cs x) = G.cprod cs (G.E a b x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [cprod_cons, cprod_cons, map_sub, map_smul, G.E_Cas, ih]

lemma comp_cprod (μ : Fin r → ℤ) (cs : List ℤ) (x : V) :
    G.comp μ (G.cprod cs x) = G.cprod cs (G.comp μ x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [cprod_cons, cprod_cons, map_sub, map_smul, G.comp_Cas, ih]

lemma sup_stable {U U' : Submodule K V} (hU : G.Stable U) (hU' : G.Stable U') : G.Stable (U ⊔ U') := by
  intro a b x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem_sup (hU a b y hy) (hU' a b z hz)

theorem chain {W V0 : Submodule K V} [FiniteDimensional K W] (hW : G.Stable W) (hWf : G.FinW W)
    (hV0 : G.Stable V0) (hV0W : V0 ≤ W) (c0 : ℤ)
    (H : ∀ U : Submodule K V, G.Stable U → V0 ≤ U → U ≤ W → ∀ μ v, v ∈ W → v ∉ U → G.IsWt μ v →
      (∀ a b, a < b → G.E a b v ∈ U) → casI μ ≠ c0) :
    ∃ cs : List ℤ, (∀ c ∈ cs, c ≠ c0) ∧ ∀ x ∈ W, G.cprod cs x ∈ V0 := by
  suffices hs : ∀ n : ℕ, ∀ U : Submodule K V, G.Stable U → V0 ≤ U → U ≤ W →
      Module.finrank K W - Module.finrank K U ≤ n →
      ∃ cs : List ℤ, (∀ c ∈ cs, c ≠ c0) ∧ ∀ x ∈ W, G.cprod cs x ∈ U from
    hs _ V0 hV0 le_rfl hV0W le_rfl
  intro n
  induction n with
  | zero =>
    intro U hU hVU hUW hn
    refine ⟨[], by simp, fun x hx => ?_⟩
    have h1 : Module.finrank K U ≤ Module.finrank K W := Submodule.finrank_mono hUW
    have hUW' : U = W := Submodule.eq_of_le_of_finrank_le hUW (by omega)
    simpa [cprod, hUW'] using hx
  | succ n ih =>
    intro U hU hVU hUW hn
    by_cases hWU : W ≤ U
    · exact ⟨[], by simp, fun x hx => by simpa [cprod] using hWU hx⟩
    obtain ⟨v, hvW, hvU, μ, hvw, hr⟩ := G.exists_hwmod (G.graded_of hW) (G.raising_of hW) hWf hWU
    let U' := U ⊔ G.gS {v}
    have hgW : G.gS {v} ≤ W := G.gS_le (by simpa using hvW) hW
    have hU' : G.Stable U' := G.sup_stable hU (G.gS_stable _)
    have hU'W : U' ≤ W := sup_le hUW hgW
    have hlt : U < U' := by
      refine lt_of_le_of_ne le_sup_left fun heq => hvU ?_
      rw [heq]; exact Submodule.mem_sup_right (G.subset_gS _ (Set.mem_singleton v))
    haveI : FiniteDimensional K U' := Submodule.finiteDimensional_of_le hU'W
    have hrk : Module.finrank K U < Module.finrank K U' := Submodule.finrank_lt_finrank_of_lt (t := U') hlt
    have hrk2 : Module.finrank K U' ≤ Module.finrank K W := Submodule.finrank_mono hU'W
    obtain ⟨cs, hcs, hx⟩ := ih U' hU' (hVU.trans le_sup_left) hU'W (by omega)
    refine ⟨casI μ :: cs, ?_, fun x hxW => ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with h | h
      · subst h; exact H U hU hVU hUW μ v hvW hvU hvw hr
      · exact hcs c h
    · rw [cprod_cons]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hx x hxW)
      rw [← hyz, map_add, smul_add, add_sub_add_comm]
      refine U.add_mem (U.sub_mem (G.Cas_mem hU hy) (U.smul_mem _ hy)) ?_
      let Q : Submodule K V := Submodule.comap (G.Cas - ((casI μ : ℤ) : K) • LinearMap.id) U
      have hQ : G.gS {v} ≤ Q := by
        apply G.gS_le
        · intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
          simpa [Q] using G.Cas_hwmod hU hvw hr
        · intro a b y hy
          simp only [Q, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
          rw [← G.E_Cas, ← map_smul, ← map_sub]; exact hU a b _ hy
      simpa [Q] using hQ hz

theorem inj_of {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {W : Submodule K V} (hW : G.Stable W)
    (hWf : G.FinW W) (hvW : v ∈ W) (Φ : V →ₗ[K] V) (κ : Fin r → ℤ)
    (hΦE : ∀ x ∈ G.gS {v}, ∀ a b, a < b → Φ (G.E a b x) = G.E a b (Φ x))
    (hΦc : ∀ x ∈ G.gS {v}, ∀ ν, Φ (G.comp ν x) = G.comp (ν + κ) (Φ x)) (hΦv : Φ v ≠ 0) :
    ∀ x ∈ G.gS {v}, Φ x = 0 → x = 0 := by
  intro x hx hΦx
  by_contra hx0
  have hgr : G.Graded (G.gS {v}) := G.graded_of (G.gS_stable {v})
  let K0 : Submodule K V :=
    { carrier := {y | y ∈ G.gS {v} ∧ Φ y = 0}
      add_mem' := fun {y z} hy hz => ⟨(G.gS {v}).add_mem hy.1 hz.1, by rw [map_add, hy.2, hz.2, add_zero]⟩
      zero_mem' := ⟨(G.gS {v}).zero_mem, map_zero Φ⟩
      smul_mem' := fun c y hy => ⟨(G.gS {v}).smul_mem c hy.1, by rw [map_smul, hy.2, smul_zero]⟩ }
  have hmemK : ∀ y, y ∈ K0 ↔ y ∈ G.gS {v} ∧ Φ y = 0 := fun y => Iff.rfl
  have hgS_W : G.gS {v} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hvW) hW
  obtain ⟨S, hS⟩ := hWf
  have hKg : G.Graded K0 := by
    intro ν y hy
    rw [hmemK] at hy ⊢
    exact ⟨hgr ν y hy.1, by rw [hΦc y hy.1, hy.2, map_zero]⟩
  have hKr : G.Raising K0 := by
    intro a b hab y hy
    rw [hmemK] at hy ⊢
    exact ⟨G.gS_stable {v} a b y hy.1, by rw [hΦE y hy.1 a b hab, hy.2, map_zero]⟩
  have hKf : G.FinW K0 := ⟨S, fun y hy ν hν => hS y (hgS_W ((hmemK y).mp hy).1) ν hν⟩
  have hnle : ¬ K0 ≤ ⊥ := by
    intro hle
    exact hx0 ((Submodule.mem_bot K).mp (hle ((hmemK x).mpr ⟨hx, hΦx⟩)))
  obtain ⟨y, hyK, hy0, μ, hyw, hyr⟩ := G.exists_hwmod hKg hKr hKf hnle
  rw [hmemK] at hyK
  have hyHW : G.IsHW μ y := ⟨hyw, fun a b hab => (Submodule.mem_bot K).mp (hyr a b hab)⟩
  have hy0' : y ≠ 0 := fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)
  obtain ⟨_, c, hc⟩ := G.hw_in_gS hv hW ⟨S, hS⟩ hvW hyK.1 hyHW hy0'
  have h1 := hyK.2
  rw [hc, map_smul] at h1
  rcases smul_eq_zero.mp h1 with h2 | h2
  · apply hy0'
    rw [hc, h2, zero_smul]
  · exact hΦv h2

end GlW

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

section Ops
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ]

private theorem pderiv_comm_lemma (y y' : σ) (F : MvPolynomial σ K) :
    pderiv y (pderiv y' F) = pderiv y' (pderiv y F) := by
  refine MvPolynomial.induction_on' F ?_ ?_
  · intro u a
    rw [pderiv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial]
    by_cases h : y = y'
    · subst h
      rfl
    · rw [tsub_right_comm]
      congr 1
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg h, if_neg (Ne.symm h), tsub_zero]
      ring
  · intro p q hp hq
    rw [map_add, map_add, hp, hq, map_add, map_add]

theorem XD_comm (x y x' y' : σ) (F : MvPolynomial σ K) :
    X x * pderiv y (X x' * pderiv y' F) - X x' * pderiv y' (X x * pderiv y F) =
      (if y = x' then X x * pderiv y' F else 0) - (if y' = x then X x' * pderiv y F else 0) := by
  rw [Derivation.leibniz, Derivation.leibniz, pderiv_X, pderiv_X, pderiv_comm_lemma y y' F]
  simp only [smul_eq_mul, Pi.single_apply, @eq_comm _ x' y, @eq_comm _ x y']
  split_ifs <;> ring

end Ops

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

open Formalism.GM.FrozenVariableComponents in
theorem top_self_comm (LL : Letters N) (i : Fin N) (a b c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i a b (top p LL i c d F) - top p LL i c d (top p LL i a b F) =
      (if b = c then top p LL i a d F else 0) - (if d = a then top p LL i c b F else 0) := by
  simp only [top_apply]
  by_cases hv : LL.vec i
  · simp only [hv, if_true]
    rw [XD_comm]
    simp only [Prod.mk.injEq, true_and]
  · simp only [hv, if_false, Bool.false_eq_true]
    simp only [map_neg, mul_neg, neg_neg, sub_neg_eq_add]
    have := XD_comm (K := ℚ_[p]) (i, b) (i, a) (i, d) (i, c) F
    simp only [Prod.mk.injEq, true_and, @eq_comm _ a d, @eq_comm _ c b] at this
    rw [this]
    split_ifs <;> (try simp) <;> abel

open Formalism.GM.FrozenVariableComponents in
theorem glAct_comm (LL : Letters N) (j : ℕ) (a b c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j a b (glAct p LL j c d F) - glAct p LL j c d (glAct p LL j a b F) =
      (if b = c then glAct p LL j a d F else 0) - (if d = a then glAct p LL j c b F else 0) := by
  classical
  set T : Fin N → Fin r → Fin r → (MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    fun i a b => if (i : ℕ) < j then top p LL i a b else 0 with hT
  have hg : ∀ a b, glAct p LL j a b = ∑ i, T i a b := fun a b => glAct_eq_top p LL j a b
  have key : glAct p LL j a b * glAct p LL j c d - glAct p LL j c d * glAct p LL j a b =
      (if b = c then glAct p LL j a d else 0) - (if d = a then glAct p LL j c b else 0) := by
    rw [hg a b, hg c d, hg a d, hg c b, Finset.sum_mul_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm (f := fun i i' => T i c d * T i' a b), ← Finset.sum_sub_distrib]
    have e1 : ∀ i, ∑ i', T i a b * T i' c d - ∑ i', T i' c d * T i a b =
        T i a b * T i c d - T i c d * T i a b := by
      intro i
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · intro i' _ hi'
        simp only [hT]
        split_ifs
        · rw [sub_eq_zero]; refine LinearMap.ext fun G => ?_; exact top_comm p LL i i' (Ne.symm hi') a b c d G
        all_goals simp
      · simp
    simp only [e1]
    have e2 : ∀ i, T i a b * T i c d - T i c d * T i a b =
        (if b = c then T i a d else 0) - (if d = a then T i c b else 0) := by
      intro i
      simp only [hT]
      by_cases hi : (i : ℕ) < j
      · simp only [hi, if_true]
        refine LinearMap.ext fun G => ?_
        simp only [LinearMap.sub_apply, Module.End.mul_apply, top_self_comm]
        split_ifs <;> simp
      · simp [hi]
    simp only [e2, Finset.sum_sub_distrib]
    split_ifs <;> simp
  have := congrArg (fun T => T F) key
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, apply_ite (fun T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] _ => T F),
    LinearMap.zero_apply] using this

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

section W
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ] {M : Type} [AddCommGroup M]

theorem XD_monomial (x y : σ) (d : σ →₀ ℕ) (a : K) :
    X y * pderiv x (monomial d a) = monomial (d - Finsupp.single x 1 + Finsupp.single y 1) (a * d x) := by
  rw [pderiv_monomial, show (X y : MvPolynomial σ K) = monomial (Finsupp.single y 1) 1 from rfl, monomial_mul,
    one_mul, add_comm (Finsupp.single y 1)]

theorem wh_XD (w : σ → M) (x y : σ) (d : σ →₀ ℕ) (a : K) :
    X y * pderiv x (monomial d a) ∈ weightedHomogeneousSubmodule K w (Finsupp.weight w d - w x + w y) := by
  rw [XD_monomial, mem_weightedHomogeneousSubmodule]
  by_cases h : d x = 0
  · rw [h, Nat.cast_zero, mul_zero, monomial_zero]
    intro m hm
    rw [coeff_zero] at hm
    exact absurd rfl hm
  · apply isWeightedHomogeneous_monomial
    have e : d - Finsupp.single x 1 + Finsupp.single x 1 = d := by
      ext z
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hz
      · subst hz
        omega
      · omega
    have hs : ∀ z : σ, Finsupp.weight w (Finsupp.single z 1) = w z := fun z => by
      rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul]
    have h2 : Finsupp.weight w (d - Finsupp.single x 1) = Finsupp.weight w d - w x := by
      conv_rhs => rw [← e]
      rw [map_add, hs, add_sub_cancel_right]
    rw [map_add, h2, hs]

theorem XD_diag (x : σ) (d : σ →₀ ℕ) (a : K) :
    X x * pderiv x (monomial d a) = (d x : K) • monomial d a := by
  rw [pderiv_monomial, show (X x : MvPolynomial σ K) = monomial (Finsupp.single x 1) 1 from rfl, monomial_mul,
    one_mul, smul_monomial, smul_eq_mul]
  by_cases h : d x = 0
  · simp [h]
  · have e : Finsupp.single x 1 + (d - Finsupp.single x 1) = d := by
      ext z
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hz
      · subst hz
        omega
      · omega
    rw [e, mul_comm]

end W

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def wv (LL : Letters N) (j : ℕ) : Fin N × Fin r → (Fin r → ℤ) := fun x =>
  if (x.1 : ℕ) < j then (if LL.vec x.1 then Pi.single x.2 1 else -Pi.single x.2 1) else 0

theorem weight_wv (LL : Letters N) (j : ℕ) (m : Fin N × Fin r →₀ ℕ) (c : Fin r) :
    Finsupp.weight (wv LL j) m c = wt LL j c m := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_prod_type]
  unfold wt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j <;> by_cases h2 : LL.vec i <;> simp [wv, h1, h2, Pi.single_apply]

open Formalism.GM.FrozenVariableComponents in
theorem glAct_diag_monomial (LL : Letters N) (j : ℕ) (c : Fin r) (d : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    glAct p LL j c c (monomial d a) = ((wt LL j c d : ℤ) : ℚ_[p]) • monomial d a := by
  unfold glAct wt
  rw [LinearMap.sum_apply, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2 <;> simp [XD_diag] <;> rw [← pderiv_monomial, XD_diag]

open Formalism.GM.FrozenVariableComponents in
theorem glAct_wh (LL : Letters N) (j : ℕ) (a b : Fin r) {ν : Fin r → ℤ} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL j) ν) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL j) (ν + dl a b) := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight (wv LL j) d = ν := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have h3 := wh_XD (K := ℚ_[p]) (wv LL j) (i, b) (i, a) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL j) d - wv LL j (i, b) + wv LL j (i, a) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [e]
    exact h3
  · have h3 := wh_XD (K := ℚ_[p]) (wv LL j) (i, a) (i, b) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL j) d - wv LL j (i, a) + wv LL j (i, b) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _

noncomputable def GA (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) :
    GlW ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) r where
  E := glAct p LL j
  comm := fun a b c d x => glAct_comm LL j a b c d x
  comp := fun μ => weightedHomogeneousComponent (wv LL j) μ
  dec := by
    classical
    intro x
    refine ⟨x.support.image (Finsupp.weight (wv LL j)), fun μ hμ => ?_⟩
    apply weightedHomogeneousComponent_eq_zero'
    intro d hd h
    exact hμ (Finset.mem_image.mpr ⟨d, hd, h⟩)
  sum_comp := by
    classical
    intro x S hS
    ext d
    rw [coeff_sum]
    simp only [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have := congrArg (coeff d) (hS _ h)
      rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
      exact this.symm
  idem := by
    classical
    intro μ ν x
    ext d
    by_cases h : μ = ν
    · subst h; simp only [if_true, coeff_weightedHomogeneousComponent]; split_ifs <;> rfl
    · simp only [if_neg h, coeff_zero, coeff_weightedHomogeneousComponent]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; exact h (h1.symm.trans h2))
  diag := by
    classical
    intro c μ x
    rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [glAct_diag_monomial, ← weight_wv, (Finset.mem_filter.mp hd).2]
  shift := by
    classical
    intro a b μ x
    have hx : x = ∑ ν ∈ x.support.image (Finsupp.weight (wv LL j)), weightedHomogeneousComponent (wv LL j) ν x := by
      ext d
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
    conv_lhs => rw [hx]
    rw [map_sum, map_sum]
    have e : ∀ ν, weightedHomogeneousComponent (wv LL j) μ (glAct p LL j a b (weightedHomogeneousComponent (wv LL j) ν x)) =
        if ν = μ - dl a b then glAct p LL j a b (weightedHomogeneousComponent (wv LL j) ν x) else 0 := by
      intro ν
      rw [weightedHomogeneousComponent_of_mem (glAct_wh LL j a b (weightedHomogeneousComponent_mem _ x ν))]
      congr 1
      apply propext; constructor <;> intro h <;> subst h <;> simp
    simp only [e, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [weightedHomogeneousComponent_eq_zero', map_zero]
      intro d hd h'
      exact h (Finset.mem_image.mpr ⟨d, hd, h'⟩)

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

theorem deriv_transfer {K σ τ : Type} [CommRing K] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (D0 : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (D1 : MvPolynomial τ K →ₗ[K] MvPolynomial τ K)
    (h0 : ∀ x y, D0 (x * y) = x * D0 y + y * D0 x) (h1 : ∀ x y, D1 (x * y) = x * D1 y + y * D1 x)
    (hg : ∀ v, D1 (φ (X v)) = φ (D0 (X v))) (f : MvPolynomial σ K) : D1 (φ f) = φ (D0 f) := by
  have hD0one : D0 1 = 0 := by simpa using h0 1 1
  have hD1one : D1 1 = 0 := by simpa using h1 1 1
  induction f using MvPolynomial.induction_on
  · rename_i a
    rw [C_eq_smul_one, map_smul φ, map_one φ, map_smul D1, map_smul D0, hD1one, hD0one, smul_zero, smul_zero,
      map_zero]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    rw [map_mul φ, h1, hg v, hp, h0, map_add φ, map_mul φ, map_mul φ]

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem glAct_X_gen (LL : Letters N) (j : ℕ) (c d : Fin r) (i : Fin N) (a : Fin r) :
    glAct p LL j c d (X (i, a)) = if (i : ℕ) < j then
      (if LL.vec i then (if a = d then X (i, c) else 0) else (if a = c then -X (i, d) else 0)) else 0 := by
  unfold glAct
  rw [LinearMap.sum_apply, Finset.sum_eq_single i]
  · split_ifs <;> simp [pderiv_X, Pi.single_apply, *]
  · intro b _ hb
    split_ifs <;> simp [pderiv_X, Pi.single_apply, hb, Ne.symm hb]
  · simp

theorem glAct_rename {M : ℕ} (LA : Letters M) (LB : Letters N) (ι : Fin M → Fin N) (hι : ∀ a, ((ι a) : ℕ) = a)
    (hv : ∀ a, LB.vec (ι a) = LA.vec a) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    rename (fun x => (ι x.1, x.2)) (glAct p LA j c d F) = glAct p LB j c d (rename (fun x => (ι x.1, x.2)) F) := by
  refine (deriv_transfer (rename (fun x : Fin M × Fin r => (ι x.1, x.2))) (glAct p LA j c d) (glAct p LB j c d)
    (fun x y => Formalism.GM.M.FB.glAct_mul LA j c d x y) (fun x y => Formalism.GM.M.FB.glAct_mul LB j c d x y) ?_ F).symm
  intro v
  obtain ⟨a, b⟩ := v
  rw [rename_X, glAct_X_gen, glAct_X_gen, hι, hv]
  split_ifs <;> simp

theorem weight_mapDomain {σ τ M : Type} [AddCommMonoid M] (w : τ → M) (f : σ → τ) (m : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f m) = Finsupp.weight (w ∘ f) m := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · rfl
  · intro b
    simp
  · intro b m1 m2
    rw [add_smul]

theorem isWH_rename {σ τ M : Type} [AddCommMonoid M] {K : Type} [CommSemiring K] (w : τ → M) (f : σ → τ)
    (hf : Function.Injective f) {F : MvPolynomial σ K} {ν : M} (hF : IsWeightedHomogeneous (w ∘ f) F ν) :
    IsWeightedHomogeneous w (rename f F) ν := by
  intro d hd
  by_contra hne
  apply hd
  apply coeff_rename_eq_zero
  intro u hu
  by_contra hu0
  apply hne
  rw [← hu, weight_mapDomain]
  exact hF hu0

theorem supp_of_supported {K σ : Type} [CommSemiring K] {s : Set σ} {q : MvPolynomial σ K}
    (hq : q ∈ MvPolynomial.supported K s) : ∀ m ∈ q.support, ∀ v, m v ≠ 0 → v ∈ s := by
  intro m hm v hv
  rw [mem_supported] at hq
  apply hq
  rw [Finset.mem_coe, mem_vars]
  exact ⟨m, hm, Finsupp.mem_support_iff.mpr hv⟩

theorem pderiv_eq_zero_of {K σ : Type} [CommRing K] {q : MvPolynomial σ K} {v : σ}
    (h : ∀ m ∈ q.support, m v = 0) : pderiv v q = 0 := by
  classical
  rw [q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [pderiv_monomial, h m hm, Nat.cast_zero, mul_zero, monomial_zero]

theorem glAct_kill (LL : Letters N) (j : ℕ) (c d : Fin r) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j → m v = 0) : glAct p LL j c d q = 0 := by
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h1 h2
  · simp [pderiv_eq_zero_of (fun m hm => hq m hm (i, d) h1)]
  · simp [pderiv_eq_zero_of (fun m hm => hq m hm (i, c) h1)]
  · simp

theorem glAct_mul_kill (LL : Letters N) (j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j → m v = 0) :
    glAct p LL j c d (x * q) = glAct p LL j c d x * q := by
  unfold glAct
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2
  · simp [Derivation.leibniz, pderiv_eq_zero_of (fun m hm => hq m hm (i, d) h1)] <;> ring
  · simp [Derivation.leibniz, pderiv_eq_zero_of (fun m hm => hq m hm (i, c) h1)] <;> ring
  · simp

theorem indep_B (j0 : ℕ) (s : Finset (Fin N × Fin r →₀ ℕ)) (a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hs : ∀ b ∈ s, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0)
    (ha : ∀ b ∈ s, ∀ m ∈ (a b).support, ∀ v : Fin N × Fin r, j0 ≤ (v.1 : ℕ) → m v = 0)
    (h0 : ∑ b ∈ s, a b * monomial b 1 = 0) : ∀ b ∈ s, a b = 0 := by
  classical
  intro b0 hb0
  ext m
  rw [coeff_zero]
  by_contra hne
  have hmA : ∀ v : Fin N × Fin r, j0 ≤ (v.1 : ℕ) → m v = 0 := ha b0 hb0 m (mem_support_iff.mpr hne)
  have := congrArg (coeff (m + b0)) h0
  rw [coeff_zero, coeff_sum, Finset.sum_eq_single b0] at this
  · rw [coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one] at this
    exact hne this
  · intro b hb hbne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · have : coeff (m + b0 - b) (a b) = 0 := by
        by_contra hc
        have hA := ha b hb (m + b0 - b) (mem_support_iff.mpr hc)
        apply hbne
        ext v
        by_cases hv : (v.1 : ℕ) < j0
        · rw [hs b hb v hv, hs b0 hb0 v hv]
        · have h1 := hA v (by omega)
          have h2 := hmA v (by omega)
          have h3 := hle v
          simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, h2, zero_add] at h1 h3
          omega
      rw [this, zero_mul]
    · rfl
  · intro h; exact absurd hb0 h

noncomputable def wL (N r : ℕ) : Fin N × Fin r → (Fin N → ℤ) := fun x => Pi.single x.1 1

theorem weight_wL (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    Finsupp.weight (wL N r) m i = ∑ c, (m (i, c) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single i]
  · simp [wL]
  · intro b _ hb
    simp [wL, Pi.single_apply, hb, Ne.symm hb]
  · simp

theorem pol_iff (LL : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ Pol p r LL ↔ IsWeightedHomogeneous (wL N r) x (fun i => (LL.deg i : ℤ)) := by
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h d hd
    have hm : MultiDeg LL d := h (mem_support_iff.mpr hd)
    funext i
    rw [weight_wL]
    exact_mod_cast hm i
  · intro h d hd
    have hw := h (mem_support_iff.mp hd)
    show ∀ i, ∑ c, d (i, c) = LL.deg i
    intro i
    have h5 := congrFun hw i
    rw [weight_wL] at h5
    exact_mod_cast h5

theorem glAct_wL (LL : Letters N) (j : ℕ) (a b : Fin r) {D : Fin N → ℤ} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wL N r) D) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wL N r) D := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight (wL N r) d = D := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have h3 := wh_XD (K := ℚ_[p]) (wL N r) (i, b) (i, a) d (coeff d x)
    have e : D = Finsupp.weight (wL N r) d - wL N r (i, b) + wL N r (i, a) := by
      rw [hwd]
      simp [wL]
    rw [e]
    exact h3
  · have h3 := wh_XD (K := ℚ_[p]) (wL N r) (i, a) (i, b) d (coeff d x)
    have e : D = Finsupp.weight (wL N r) d - wL N r (i, a) + wL N r (i, b) := by
      rw [hwd]
      simp [wL]
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem glAct_pol (LL L2 : Letters N) (j : ℕ) (a b : Fin r) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L2) : glAct p LL j a b x ∈ Pol p r L2 := by
  rw [pol_iff] at hx ⊢
  have h := glAct_wL LL j a b (by rw [mem_weightedHomogeneousSubmodule]; exact hx)
  rw [mem_weightedHomogeneousSubmodule] at h
  exact h

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem wt_add (LL : Letters N) (j : ℕ) (c : Fin r) (m m' : Fin N × Fin r →₀ ℕ) :
    wt LL j c (m + m') = wt LL j c m + wt LL j c m' := by
  unfold wt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finsupp.add_apply, Nat.cast_add]
  split_ifs <;> ring

theorem glAct_wh' (LL : Letters N) {j J : ℕ} (hjJ : j ≤ J) (a b : Fin r) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) (ν + dl a b) := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight (wv LL J) d = ν := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1' h2
  · have h1 : (i : ℕ) < J := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, b) (i, a) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL J) d - wv LL J (i, b) + wv LL J (i, a) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [e]
    exact h3
  · have h1 : (i : ℕ) < J := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, a) (i, b) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL J) d - wv LL J (i, a) + wv LL J (i, b) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _

private theorem rM_of_wh_lemma [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) (ν : Fin r → ℤ)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hz : z ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν)
    (hν : ((ν 0 : ℤ) : WithTop ℤ) ≤ M) :
    z ∈ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M} := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  rw [mem_weightedHomogeneousSubmodule] at hz
  have h1 := hz (mem_support_iff.mp hm)
  show ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M
  rw [← weight_wv, h1]
  exact hν

private theorem ycond_stable_lemma_2 [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) :
    GlStable p LL J (YCond p (r := r) LL J M) := by
  intro c d x hx
  have hle : YCond p (r := r) LL J M ≤ (YCond p (r := r) LL J M).comap (glAct p LL J c d) := by
    unfold YCond
    apply sSup_le
    intro S hS y hy
    exact le_sSup hS (hS.2 c d y hy)
  exact hle hx

theorem ycond_of_comm [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d F, A (glAct p LL J c d F) = glAct p LL J c d (A F))
    (hw : ∀ ν F, F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν →
      A F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    ∀ F ∈ YCond p LL J M, A F ∈ YCond p LL J M := by
  intro F hF
  have hYR : YCond p (r := r) LL J M ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M} :=
    sSup_le fun S hS => hS.1
  have hYst : GlStable p LL J (YCond p (r := r) LL J M) := ycond_stable_lemma_2 LL J M
  have hmap : (YCond p (r := r) LL J M).map A ≤ YCond p (r := r) LL J M := by
    apply le_sSup
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have hyR := hYR hy
      rw [MvPolynomial.mem_restrictSupport_iff] at hyR
      classical
      have hsum : y = ∑ ν ∈ y.support.image (Finsupp.weight (wv LL J)),
          weightedHomogeneousComponent (wv LL J) ν y := by
        ext d
        rw [coeff_sum]
        simp only [coeff_weightedHomogeneousComponent]
        rw [Finset.sum_ite_eq]
        split_ifs with h
        · rfl
        · by_contra hne
          exact h (Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hne, rfl⟩)
      rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun ν hν => ?_
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hν
      apply rM_of_wh_lemma LL J M
      · exact hw _ _ (weightedHomogeneousComponent_mem _ y _)
      · have h2 : ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M := hyR hm
        rw [← weight_wv] at h2
        exact h2
    · intro c d x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      rw [← hc]
      exact Submodule.mem_map_of_mem (hYst c d y hy)
  exact hmap (Submodule.mem_map_of_mem hF)

theorem ycond_mul_B [NeZero r] (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ)
    {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    ∀ F ∈ YCond p LL J M, q * F ∈ YCond p LL J M := by
  refine ycond_of_comm LL J M (LinearMap.mulLeft ℚ_[p] q) ?_ ?_
  · intro c d G
    simp only [LinearMap.mulLeft_apply]
    rw [mul_comm q, mul_comm q, glAct_mul_kill LL J c d G (fun m hm v hv => hq m hm v (by omega))]
  · intro ν G hG
    simp only [LinearMap.mulLeft_apply]
    have hq0 : q ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) 0 := by
      rw [mem_weightedHomogeneousSubmodule]
      intro m hm
      rw [Finsupp.weight_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases h : (v.1 : ℕ) < J
      · rw [hq m (mem_support_iff.mpr hm) v (by omega), zero_smul]
      · simp [wv, h]
    rw [mem_weightedHomogeneousSubmodule] at hG hq0 ⊢
    have h5 := hq0.mul hG
    rwa [zero_add] at h5

noncomputable def midAct (p : ℕ) [Fact p.Prime] (LL : Letters N) (J j0 : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ∑ i : Fin N, if J ≤ (i : ℕ) ∧ (i : ℕ) < j0 then Formalism.GM.FrozenVariableComponents.top p LL i c d else 0

theorem glAct_split (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (c d : Fin r) :
    glAct p LL j0 c d = glAct p LL J c d + midAct p LL J j0 c d := by
  unfold glAct midAct
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < J
  · have h2 : (i : ℕ) < j0 := by omega
    have h3 : ¬ (J ≤ (i : ℕ) ∧ (i : ℕ) < j0) := fun h => by omega
    simp [h1, h2, h3]
  · by_cases h2 : (i : ℕ) < j0
    · have h3 : J ≤ (i : ℕ) := by omega
      simp [h1, h2, h3, Formalism.GM.FrozenVariableComponents.top]
    · simp [h1, h2]

private theorem top_comm_lemma (LL : Letters N) (i i' : Fin N) (hne : i ≠ i') (a b c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    Formalism.GM.FrozenVariableComponents.top p LL i a b (Formalism.GM.FrozenVariableComponents.top p LL i' c d F) =
      Formalism.GM.FrozenVariableComponents.top p LL i' c d (Formalism.GM.FrozenVariableComponents.top p LL i a b F) := by
  have key : ∀ (x y x' y' : Fin N × Fin r), x.1 = i → y.1 = i → x'.1 = i' → y'.1 = i' →
      ∀ G : MvPolynomial (Fin N × Fin r) ℚ_[p],
      X x * pderiv y (X x' * pderiv y' G) = X x' * pderiv y' (X x * pderiv y G) := by
    intro x y x' y' hx hy hx' hy' G
    have h := XD_comm x y x' y' G
    rw [if_neg (fun h' => hne (by rw [← hy, h', hx'])), if_neg (fun h' => hne (by rw [← hx, ← h', hy'])),
      sub_zero, sub_eq_zero] at h
    exact h
  unfold Formalism.GM.FrozenVariableComponents.top
  by_cases hv : LL.vec i <;> by_cases hv' : LL.vec i' <;>
    simp only [hv, hv', if_true, if_false, ite_true, ite_false, Bool.false_eq_true, LinearMap.neg_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, map_neg, mul_neg, neg_neg, neg_inj] <;>
    first
      | exact key _ _ _ _ rfl rfl rfl rfl F
      | exact key (i, a) (i, b) (i', c) (i', d) rfl rfl rfl rfl F
      | exact key (i, a) (i, b) (i', d) (i', c) rfl rfl rfl rfl F
      | exact key (i, b) (i, a) (i', c) (i', d) rfl rfl rfl rfl F
      | exact key (i, b) (i, a) (i', d) (i', c) rfl rfl rfl rfl F

theorem midAct_comm (LL : Letters N) (J j0 : ℕ) (c d c' d' : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    midAct p LL J j0 c d (glAct p LL J c' d' F) = glAct p LL J c' d' (midAct p LL J j0 c d F) := by
  unfold midAct glAct
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  by_cases h1 : J ≤ (i : ℕ) ∧ (i : ℕ) < j0
  · by_cases h2 : (i' : ℕ) < J
    · have hne : i ≠ i' := fun h => by subst h; omega
      rw [if_pos h1, if_pos h2]
      exact top_comm_lemma LL i i' hne c d c' d' F
    · simp [h2]
  · simp [h1]

theorem midAct_wh (LL : Letters N) (J j0 : ℕ) (c d : Fin r) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    midAct p LL J j0 c d x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hwd : Finsupp.weight (wv LL J) m = ν := hx (mem_support_iff.mp hm)
  unfold midAct Formalism.GM.FrozenVariableComponents.top
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have hnJ : ¬ ((i : ℕ) < J) := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, d) (i, c) m (coeff m x)
    have e : ν = Finsupp.weight (wv LL J) m - wv LL J (i, d) + wv LL J (i, c) := by
      rw [hwd]
      simp [wv, hnJ]
    rw [e]
    exact h3
  · have hnJ : ¬ ((i : ℕ) < J) := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, c) (i, d) m (coeff m x)
    have e : ν = Finsupp.weight (wv LL J) m - wv LL J (i, c) + wv LL J (i, d) := by
      rw [hwd]
      simp [wv, hnJ]
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem ycond_glAct_le [NeZero r] (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (c d : Fin r)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p LL J M) :
    glAct p LL j0 c d F ∈ YCond p LL J M := by
  rw [glAct_split LL hJ c d, LinearMap.add_apply]
  exact Submodule.add_mem _ (ycond_stable_lemma_2 LL J M c d F hF)
    (ycond_of_comm LL J M (midAct p LL J j0 c d) (fun c' d' G => midAct_comm LL J j0 c d c' d' G)
      (fun ν G hG => midAct_wh LL J j0 c d hG) F hF)

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Cas_comm_glAct (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p LL j0).Cas (glAct p LL J c d F) = glAct p LL J c d ((GA p LL j0).Cas F) := by
  rw [glAct_split LL hJ c d, LinearMap.add_apply, LinearMap.add_apply, map_add]
  congr 1
  · exact ((GA p LL j0).E_Cas c d F).symm
  · rw [GlW.Cas_apply, GlW.Cas_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show glAct p LL j0 a b (glAct p LL j0 b a (midAct p LL j0 J c d F)) =
      midAct p LL j0 J c d (glAct p LL j0 a b (glAct p LL j0 b a F))
    rw [← midAct_comm, ← midAct_comm]

theorem Cas_wh (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {F : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    (GA p LL j0).Cas F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν := by
  rw [GlW.Cas_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  have h1 := glAct_wh' LL hJ b a hF
  have h2 := glAct_wh' LL hJ a b h1
  have e : ν + dl b a + dl a b = ν := by
    funext c
    simp only [Pi.add_apply, dl_apply]
    split_ifs <;> omega
  rw [e] at h2
  exact h2

theorem ycond_cprod [NeZero r] (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (M : WithTop ℤ) (cs : List ℤ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p LL J M) :
    (GA p LL j0).cprod cs F ∈ YCond p LL J M := by
  refine ycond_of_comm LL J M ((GA p LL j0).cprod cs) ?_ ?_ F hF
  · intro c d G
    induction cs with
    | nil => rfl
    | cons c0 cs ih =>
      rw [GlW.cprod_cons, GlW.cprod_cons, ih, Cas_comm_glAct LL hJ, map_sub, map_smul]
  · intro ν G hG
    induction cs with
    | nil => exact hG
    | cons c0 cs ih =>
      rw [GlW.cprod_cons]
      exact Submodule.sub_mem _ (Cas_wh LL hJ ih) (Submodule.smul_mem _ _ ih)

theorem glAct_lw {M : Type} [AddCommGroup M] (LL : Letters N) (j : ℕ) (a b : Fin r) (w : Fin N × Fin r → M)
    (hw : ∀ i c c', w (i, c) = w (i, c')) {D : M} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight w d = D := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have h3 := wh_XD (K := ℚ_[p]) w (i, b) (i, a) d (coeff d x)
    have e : D = Finsupp.weight w d - w (i, b) + w (i, a) := by
      rw [hwd, hw i b a, sub_add_cancel]
    rw [e]
    exact h3
  · have h3 := wh_XD (K := ℚ_[p]) w (i, a) (i, b) d (coeff d x)
    have e : D = Finsupp.weight w d - w (i, a) + w (i, b) := by
      rw [hwd, hw i a b, sub_add_cancel]
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _

noncomputable def wOut (N r : ℕ) (i0 : Fin N) : Fin N × Fin r → ℤ := fun v => if v.1 = i0 then 0 else 1

theorem wOut_zero {i0 : Fin N} {m : Fin N × Fin r →₀ ℕ} (h : Finsupp.weight (wOut N r i0) m = 0) :
    ∀ v : Fin N × Fin r, v.1 ≠ i0 → m v = 0 := by
  intro v hv
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)] at h
  have hnn : ∀ x ∈ (Finset.univ : Finset (Fin N × Fin r)), 0 ≤ m x • wOut N r i0 x := by
    intro x _
    unfold wOut
    split_ifs <;> simp
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h v (Finset.mem_univ v)
  simp only [wOut, if_neg hv, nsmul_eq_mul, mul_one] at h2
  exact_mod_cast h2

theorem ycond_mul_cov [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) (i0 : Fin N) (hi0 : (i0 : ℕ) < J)
    (hv : LL.vec i0 = false) {e : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (he : e ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r i0) 0) :
    ∀ F ∈ YCond p LL J M, e * F ∈ YCond p LL J M := by
  classical
  let H := weightedHomogeneousSubmodule ℚ_[p] (wOut N r i0) 0
  have hH : ∀ c d, ∀ x ∈ H, glAct p LL J c d x ∈ H := fun c d x hx =>
    glAct_lw LL J c d (wOut N r i0) (fun i c c' => rfl) hx
  let S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Submodule.span ℚ_[p] {x | ∃ e ∈ H, ∃ y ∈ YCond p LL J M, x = e * y}
  have hwa : ∀ a : Fin N × Fin r →₀ ℕ, Finsupp.weight (wOut N r i0) a = 0 → wt LL J 0 a ≤ 0 := by
    intro a ha
    have hz := wOut_zero ha
    unfold wt
    rw [Finset.sum_eq_single i0]
    · simp [hi0, hv]
    · intro b _ hb; rw [hz (b, 0) hb]; simp
    · simp
  have hS1 : S ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL J 0 m : ℤ) : WithTop ℤ) ≤ M} := by
    rw [Submodule.span_le]
    rintro _ ⟨e, he, y, hy, rfl⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul e y hm)
    have h1 := hwa a (he (mem_support_iff.mp ha))
    have h2 := Formalism.GM.FrozenVariableComponents.wt_le_of_mem p LL J M y hy b hb
    show ((wt LL J 0 (a + b) : ℤ) : WithTop ℤ) ≤ M
    rw [wt_add]
    induction M using WithTop.recTopCoe with
    | top => exact le_top
    | coe M' =>
      rw [WithTop.coe_le_coe] at h2 ⊢
      omega
  have hS2 : GlStable p LL J S := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, y, hy, rfl⟩ := hx
      rw [Formalism.GM.M.FB.glAct_mul]
      refine S.add_mem (Submodule.subset_span ⟨e, he, _, Formalism.GM.FrozenVariableComponents.ycond_stable p LL J M c d y hy, rfl⟩) ?_
      rw [mul_comm]
      exact Submodule.subset_span ⟨_, hH c d e he, y, hy, rfl⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S.smul_mem a hx
  have hS : S ≤ YCond p LL J M := le_sSup ⟨hS1, hS2⟩
  intro F hF
  exact hS (Submodule.subset_span ⟨e, he, F, hF, rfl⟩)

theorem pol_finite (LL : Letters N) : Set.Finite {m : Fin N × Fin r →₀ ℕ | MultiDeg LL m} := by
  classical
  apply Set.Finite.subset (Set.finite_range (fun g : Fin N × Fin r → Fin (∑ i, LL.deg i + 1) =>
    Finsupp.equivFunOnFinite.symm (fun x => (g x : ℕ))))
  intro m hm
  have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
  have hb : ∀ x : Fin N × Fin r, m x < ∑ i, LL.deg i + 1 := by
    rintro ⟨i, c⟩
    have h1 : m (i, c) ≤ ∑ c', m (i, c') :=
      Finset.single_le_sum (f := fun c' => m (i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    have h2 : LL.deg i ≤ ∑ i', LL.deg i' :=
      Finset.single_le_sum (f := fun i' => LL.deg i') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hm' i] at h1
    omega
  refine ⟨fun x => ⟨m x, hb x⟩, ?_⟩
  ext x
  simp

theorem pol_fd (LL : Letters N) : FiniteDimensional ℚ_[p] (Pol p r LL) := by
  haveI := FiniteDimensional.span_of_finite ℚ_[p]
    ((pol_finite (r := r) LL).image (fun m => monomial m (1 : ℚ_[p])))
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[p] ((fun m => monomial m (1 : ℚ_[p])) '' {m : Fin N × Fin r →₀ ℕ | MultiDeg LL m})) ?_
  intro x hx
  unfold Pol at hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [show monomial m (coeff m x) = coeff m x • monomial m (1 : ℚ_[p]) by rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hx hm, rfl⟩)

theorem pol_finW (LL : Letters N) (j : ℕ) : (GA p LL j).FinW (Pol p r LL) := by
  classical
  refine ⟨(pol_finite (r := r) LL).toFinset.image (Finsupp.weight (wv LL j)), fun x hx μ hμ => ?_⟩
  show weightedHomogeneousComponent (wv LL j) μ x = 0
  unfold Pol at hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd hw
  apply hμ
  rw [Finset.mem_image]
  refine ⟨d, ?_, hw⟩
  rw [Set.Finite.mem_toFinset]
  exact hx hd

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

theorem aeval_isWH' {σ τ R M : Type} [CommSemiring R] [AddCommMonoid M] (w' : σ → M) (w : τ → M)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : M} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have hmd : Finsupp.weight w' m = d := hf (mem_support_iff.mp hm)
  rw [← hmd, Finsupp.weight_apply]
  apply IsWeightedHomogeneous.C_mul
  exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hg i).pow (m i))

theorem isWH_hom {σ R M M' : Type} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M'] (E : M →+ M')
    (w : σ → M) {F : MvPolynomial σ R} {ν : M} (h : IsWeightedHomogeneous w F ν) :
    IsWeightedHomogeneous (E ∘ w) F (E ν) := by
  intro d hd
  rw [← h hd, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
  simp only [Function.comp_apply, map_nsmul]

private theorem glAct_leib_lemma {N r : ℕ} {p : ℕ} [Fact p.Prime] (LL : Letters N) (j : ℕ) (c d : Fin r)
    (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (x * y) = x * glAct p LL j c d y + y * glAct p LL j c d x := by
  unfold glAct
  simp only [LinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring

theorem glAct_pow_zero {N r : ℕ} {p : ℕ} [Fact p.Prime] (LL : Letters N) (j : ℕ) (c d : Fin r)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : glAct p LL j c d x = 0) (k : ℕ) :
    glAct p LL j c d (x ^ k) = 0 := by
  induction k with
  | zero => simpa using glAct_leib_lemma LL j c d (1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) 1
  | succ k ih => rw [pow_succ, glAct_leib_lemma, ih, hx, mul_zero, mul_zero, add_zero]

variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

open Formalism.GM.M.FB in
theorem glAct_freezeSub_gen (LL : Letters K) (n : ℕ) (ρ a b : Fin r) (ha : a ≠ ρ) (hb : b ≠ ρ)
    (v : Fin K × Fin r) :
    glAct p (LL.snoc n) (K + 1) a b (freezeSub p LL ρ v) = aeval (freezeSub p LL ρ) (glAct p LL K a b (X v)) := by
  classical
  obtain ⟨i, c'⟩ := v
  rw [glAct_X]
  by_cases h1 : LL.vec i
  · by_cases h2 : c' = ρ
    · subst h2
      simp only [freezeSub, h1, if_true, map_sum, glAct_mul, glAct_X, snoc_vec_last, snoc_vec_castSucc]
      simp [mul_ite, Finset.sum_add_distrib, ha, hb, Ne.symm hb, Ne.symm ha]
      try ring
    · simp only [freezeSub, h1, h2, if_true, if_false, glAct_mul, glAct_X, snoc_vec_last, snoc_vec_castSucc]
      by_cases h3 : c' = b
      · subst h3; simp [h2, Ne.symm h2, ha, Ne.symm ha, freezeSub, h1]; try ring
      · simp [h2, Ne.symm h2, h3, ha, Ne.symm ha]
  · by_cases h2 : c' = ρ
    · subst h2
      simp only [freezeSub, h1, if_true, if_false, Bool.false_eq_true, glAct_mul, glAct_X, snoc_vec_last,
        snoc_vec_castSucc]
      simp [ha, Ne.symm ha]
    · simp only [freezeSub, h1, h2, if_true, if_false, Bool.false_eq_true, glAct_mul, glAct_X, snoc_vec_last,
        snoc_vec_castSucc, map_sub]
      by_cases h3 : c' = a
      · subst h3; simp [h2, Ne.symm h2, hb, Ne.symm hb, freezeSub, h1]; try ring
      · simp [h2, Ne.symm h2, h3, ha, Ne.symm ha]

theorem glAct_freeze_gen (LL : Letters K) (n : ℕ) (ρ a b : Fin r) (ha : a ≠ ρ) (hb : b ≠ ρ)
    (f : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (K + 1) a b (freeze p LL ρ n f) = freeze p LL ρ n (glAct p LL K a b f) := by
  unfold freeze
  rw [Formalism.GM.M.FB.glAct_mul]
  have hX : glAct p (LL.snoc n) (K + 1) a b (X (Fin.last K, ρ)) = 0 := by
    rw [Formalism.GM.M.FB.glAct_X]; simp [Ne.symm ha]
  rw [glAct_pow_zero _ _ _ _ hX, mul_zero, add_zero]
  congr 1
  exact deriv_transfer (aeval (freezeSub p LL ρ)) (glAct p LL K a b) (glAct p (LL.snoc n) (K + 1) a b)
    (fun x y => Formalism.GM.M.FB.glAct_mul LL K a b x y) (fun x y => Formalism.GM.M.FB.glAct_mul (LL.snoc n) (K + 1) a b x y)
    (fun v => by rw [aeval_X]; exact glAct_freezeSub_gen LL n ρ a b ha hb v) f

theorem wv_snoc_castSucc (LL : Letters K) (n : ℕ) (i : Fin K) (c : Fin r) :
    wv (LL.snoc n) (K + 1) (Fin.castSucc i, c) = wv LL K (i, c) := by
  simp [wv, Formalism.GM.M.FB.snoc_vec_castSucc, i.isLt, (by omega : (i : ℕ) < K + 1)]

theorem wv_snoc_last (LL : Letters K) (n : ℕ) (c : Fin r) :
    wv (LL.snoc n) (K + 1) (Fin.last K, c) = -Pi.single c 1 := by
  simp [wv, Formalism.GM.M.FB.snoc_vec_last]

theorem freezeSub_wh (LL : Letters K) (n : ℕ) (ρ : Fin r) (v : Fin K × Fin r) :
    IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (freezeSub p LL ρ v) (wv LL K v - Pi.single ρ 1) := by
  classical
  obtain ⟨i, c⟩ := v
  have hX : ∀ x, IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (X x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
      (wv (LL.snoc n) (K + 1) x) := fun x => isWeightedHomogeneous_X _ _ x
  have hwi : ∀ c : Fin r, wv LL K (i, c) = if LL.vec i then Pi.single c 1 else -Pi.single c 1 := by
    intro c; simp [wv, i.isLt]
  by_cases h1 : LL.vec i
  · by_cases h2 : c = ρ
    · subst h2
      simp only [freezeSub, h1, if_true]
      apply IsWeightedHomogeneous.sum
      intro c' _
      have := (hX (Fin.castSucc i, c')).mul (hX (Fin.last K, c'))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_pos h1] at this
      convert this using 1
      rw [hwi, if_pos h1]; abel
    · simp only [freezeSub, h1, h2, if_true, if_false]
      have := (hX (Fin.last K, ρ)).mul (hX (Fin.castSucc i, c))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_pos h1] at this
      convert this using 1
      rw [hwi, if_pos h1]; abel
  · by_cases h2 : c = ρ
    · subst h2
      simp only [freezeSub, h1, if_true, if_false, Bool.false_eq_true]
      have := (hX (Fin.last K, c)).mul (hX (Fin.castSucc i, c))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_neg h1] at this
      convert this using 1
      rw [hwi, if_neg h1]; abel
    · simp only [freezeSub, h1, h2, if_true, if_false, Bool.false_eq_true]
      have e1 := (hX (Fin.last K, ρ)).mul (hX (Fin.castSucc i, c))
      have e2 := (hX (Fin.castSucc i, ρ)).mul (hX (Fin.last K, c))
      rw [wv_snoc_castSucc, wv_snoc_last, hwi, if_neg h1] at e1 e2
      rw [← mem_weightedHomogeneousSubmodule] at e1 e2 ⊢
      have e3 := Submodule.sub_mem _ e1 (show _ ∈ weightedHomogeneousSubmodule ℚ_[p] (wv (LL.snoc n) (K + 1))
        (-Pi.single ρ 1 + -Pi.single c 1) from by convert e2 using 2; try abel)
      convert e3 using 2
      rw [hwi, if_neg h1]; abel

theorem freeze_wh (LL : Letters K) (ρ : Fin r) (n : ℕ) (hn : LL.total ≤ n) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin K × Fin r) ℚ_[p]) (hfP : f ∈ Pol p r LL) (hfw : f ∈ WtSpC p LL K univ w) :
    IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (freeze p LL ρ n f) (w - (n : ℤ) • Pi.single ρ 1) := by
  classical
  let w' : Fin K × Fin r → (Fin r → ℤ) := fun v => wv LL K v - Pi.single ρ 1
  have hf' : IsWeightedHomogeneous w' f (w - (LL.total : ℤ) • Pi.single ρ 1) := by
    intro m hm
    have hm' : m ∈ f.support := mem_support_iff.mpr hm
    have e1 : Finsupp.weight (wv LL K) m = w := by
      funext c
      rw [weight_wv]
      have h0 : m ∈ {m : Fin K × Fin r →₀ ℕ | ∀ c ∈ (univ : Finset (Fin r)), wt LL K c m = w c} :=
        (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hfw hm'
      exact h0 c (Finset.mem_univ c)
    have e2 : ∑ v, m v = LL.total := by
      have := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hfP hm'
      rw [Fintype.sum_prod_type, Letters.total]
      exact Finset.sum_congr rfl fun i _ => this i
    have e3 : Finsupp.weight w' m = Finsupp.weight (wv LL K) m - ((∑ v, m v : ℕ) : ℤ) • Pi.single ρ 1 := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
        Finsupp.sum_fintype _ _ (by simp)]
      simp only [w', smul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_smul, natCast_zsmul]
    rw [e3, e1, e2]
  have h1 := aeval_isWH' w' (wv (LL.snoc n) (K + 1)) (freezeSub p LL ρ) (fun v => freezeSub_wh LL n ρ v) hf'
  have h2 := (isWeightedHomogeneous_X ℚ_[p] (wv (LL.snoc n) (K + 1)) (Fin.last K, ρ)).pow (n - LL.total)
  have h3 := h2.mul h1
  unfold freeze
  convert h3 using 1
  rw [wv_snoc_last]
  rw [show ((n : ℤ)) = ((n - LL.total : ℕ) : ℤ) + (LL.total : ℤ) by push_cast [Nat.cast_sub hn]; ring]
  rw [add_smul, smul_neg, ← natCast_zsmul]
  abel

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def ιF (N K : ℕ) [NeZero N] : Fin (K + 1) → Fin N :=
  fun a => if h : (a : ℕ) < N then ⟨a, h⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩

lemma ιF_val [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) (a : Fin (K + 1)) : ((ιF N K a) : ℕ) = a := by
  unfold ιF
  split_ifs with h
  · rfl
  · exact absurd (lt_of_lt_of_le a.isLt hK) h

lemma ιF_inj [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) : Function.Injective (ιF N K) := by
  intro a b h
  apply Fin.ext
  rw [← ιF_val hK a, ← ιF_val hK b, h]

lemma inclusion_prodMap_injective [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) :
    Function.Injective (fun x : Fin (K + 1) × Fin r => (ιF N K x.1, x.2)) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (ιF_inj hK h.1) h.2

lemma Ffull_eq [NeZero N] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.Ffull p LL i ρ n f = rename (fun x => (ιF N (T.pos i + 1) x.1, x.2)) (freeze p (LL.takeD (T.pos i + 1)) ρ n f) :=
  rfl

lemma hK_of_adm (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) : T.pos i + 1 + 1 ≤ N := by
  obtain ⟨h, -⟩ := hadm.2.1 i; omega

lemma vec_eta (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (h : T.pos i + 1 < N) :
    LL.vec ⟨T.pos i + 1, h⟩ = false := by
  obtain ⟨h', -, h2⟩ := hadm.2.1 i; exact h2

lemma choose_tie (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (h : ∃ j, T.pos j + 1 = T.pos i + 1) : Classical.choose h = i := by
  have := Classical.choose_spec h
  exact hadm.1.injective (by omega)

lemma setTies_deg_eta (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ)
    (h : T.pos i + 1 < N) : (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by
  have hex : ∃ j, T.pos j + 1 = ((⟨T.pos i + 1, h⟩ : Fin N) : ℕ) := ⟨i, rfl⟩
  simp only [Letters.setTies, dif_pos hex]
  rw [choose_tie LL T hadm i hex]

lemma takeD_update (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ) (n' : ℕ) :
    (LL.setTies T (Function.update n i n')).takeD (T.pos i + 1) = (LL.setTies T n).takeD (T.pos i + 1) := by
  simp only [Letters.takeD]
  congr 1
  funext a
  split_ifs with h1
  · simp only [Letters.setTies]
    split_ifs with h2
    · have hne : Classical.choose h2 ≠ i := by
        intro he
        have := Classical.choose_spec h2
        rw [he] at this
        have := a.isLt
        omega
      rw [Function.update_of_ne hne]
    · rfl
  · rfl

lemma vec_compat [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (n : Fin T.t → ℕ) (m0 : ℕ) (a : Fin (T.pos i + 1 + 1)) :
    LL.vec (ιF N (T.pos i + 1) a) = (((LL.setTies T n).takeD (T.pos i + 1)).snoc m0).vec a := by
  have hK := hK_of_adm LL T hadm i
  induction a using Fin.lastCases with
  | last =>
    rw [Formalism.GM.M.FB.snoc_vec_last]
    have : ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) = ⟨T.pos i + 1, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]; exact vec_eta LL T hadm i _
  | cast a =>
    rw [Formalism.GM.M.FB.snoc_vec_castSucc]
    have : ιF N (T.pos i + 1) (Fin.castSucc a) = ⟨a, by omega⟩ := by
      apply Fin.ext; rw [ιF_val hK]; simp
    rw [this]
    simp [Letters.takeD, Letters.setTies, (by omega : (a : ℕ) < N)]

lemma wv_compat [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (n : Fin T.t → ℕ) (m0 : ℕ) (J : ℕ) :
    (wv LL J) ∘ (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) =
      wv (((LL.setTies T n).takeD (T.pos i + 1)).snoc m0) J := by
  have hK := hK_of_adm LL T hadm i
  funext x
  simp only [Function.comp, wv, ιF_val hK, vec_compat LL T hadm i n m0]

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem ycond_top [NeZero r] (LL : Letters N) (j : ℕ) : YCond p (r := r) LL j ⊤ = ⊤ := by
  unfold YCond
  apply eq_top_iff.mpr
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  constructor
  · intro x _
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m _
    show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ⊤
    exact le_top
  · intro c d x _
    exact Submodule.mem_top

theorem freeze_zero {K : ℕ} (LL : Letters K) (ρ : Fin r) (n : ℕ) :
    freeze p LL ρ n (0 : MvPolynomial (Fin K × Fin r) ℚ_[p]) = 0 := by
  simp [freeze]

section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

theorem Ffull_hw [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    (GA p LL (T.pos i + 1 + 1)).IsHW (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  obtain ⟨⟨hY, hH⟩, hW⟩ := Submodule.mem_inf.mp hf |>.imp_left Submodule.mem_inf.mp
  have hP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hY).1
  refine ⟨?_, fun a b hab => ?_⟩
  · have hwh := freeze_wh LLK ρ (n i) hS w f hP hW
    rw [← wv_compat LL T hadm i n (n i) (T.pos i + 1 + 1)] at hwh
    have := isWH_rename (K := ℚ_[p]) (wv LL (T.pos i + 1 + 1)) _ (inclusion_prodMap_injective (r := r) hK) hwh
    show weightedHomogeneousComponent _ _ _ = _
    rw [Ffull_eq, weightedHomogeneousComponent_of_mem this, if_pos rfl]
  · show glAct p LL (T.pos i + 1 + 1) a b (T.Ffull p (LL.setTies T n) i ρ (n i) f) = 0
    rw [Ffull_eq, ← glAct_rename (LA := LLK.snoc (n i)) (LB := LL) (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a)]
    have h0 : glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b (freeze p LLK ρ (n i) f) = 0 := by
      by_cases hb : b = ρ
      · subst hb
        have := (Formalism.GM.extendMapsTo p (T.pos i + 1) r LLK b (n i) hS f hP).2.1
        exact this a (ne_of_lt hab)
      · have hbr : (b : ℕ) ≤ r - 1 := by have := b.isLt; omega
        have ha : a ≠ ρ := by
          intro h; subst h
          have : (a : ℕ) < b := hab
          omega
        rw [glAct_freeze_gen LLK (n i) ρ a b ha hb]
        have hk : glAct p LLK (T.pos i + 1) a b f = 0 := by
          have := (Submodule.mem_inf.mp hH).2
          rw [Submodule.mem_iInf] at this
          have := this a
          rw [Submodule.mem_iInf] at this
          have := this b
          rw [Submodule.mem_iInf] at this
          exact this ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩, hab⟩
        rw [hk, freeze_zero]
    rw [h0, map_zero]

end Comparison₂

section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)

include hadm

theorem Ffull_ne [NeZero r] (ρ : Fin r) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) (hf0 : f ≠ 0)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ≠ 0 := by
  have hK := hK_of_adm LL T hadm i
  have hP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  intro h0
  rw [Ffull_eq] at h0
  have h1 : freeze p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) f = 0 := by
    apply rename_injective _ (inclusion_prodMap_injective (r := r) hK)
    rw [h0, map_zero]
  have := (Formalism.GM.extendBijOn p (T.pos i + 1) r ((LL.setTies T n).takeD (T.pos i + 1)) ρ (n i) hS).1 f hP 0
    (Submodule.zero_mem _) (by rw [h1, freeze_zero])
  exact hf0 this

def Lz (LL : Letters N) (j0 : ℕ) : Letters N where
  vec := LL.vec
  deg := fun a => if (a : ℕ) < j0 then LL.deg a else 0

theorem Ffull_pol (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hfP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1)) := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have h1 := (Formalism.GM.extendMapsTo p (T.pos i + 1) r LLK ρ (n i) hS f hfP).1
  rw [pol_iff] at h1 ⊢
  let E : (Fin (T.pos i + 1 + 1) → ℤ) →+ (Fin N → ℤ) :=
    { toFun := fun g b => if h : (b : ℕ) < T.pos i + 1 + 1 then g ⟨b, h⟩ else 0
      map_zero' := by funext b; simp
      map_add' := by intro g g'; funext b; simp only [Pi.add_apply]; split_ifs <;> simp }
  have h2 := isWH_hom E _ h1
  have hw : E ∘ wL (T.pos i + 1 + 1) r = wL N r ∘ (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) := by
    funext x b
    simp only [Function.comp, E, AddMonoidHom.coe_mk, ZeroHom.coe_mk, wL]
    by_cases h : b = ιF N (T.pos i + 1) x.1
    · subst h
      have hlt : ((ιF N (T.pos i + 1) x.1 : Fin N) : ℕ) < T.pos i + 1 + 1 := by rw [ιF_val hK]; exact x.1.isLt
      rw [dif_pos hlt, Pi.single_eq_same]
      have : (⟨_, hlt⟩ : Fin (T.pos i + 1 + 1)) = x.1 := Fin.ext (ιF_val hK _)
      rw [this, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]
      split_ifs with hb
      · rw [Pi.single_eq_of_ne]
        intro h'; apply h; apply Fin.ext; rw [ιF_val hK, ← h']
      · rfl
  rw [hw] at h2
  have h3 := isWH_rename (K := ℚ_[p]) (wL N r) _ (inclusion_prodMap_injective (r := r) hK) h2
  rw [Ffull_eq]
  convert h3 using 1
  funext b
  simp only [E, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Lz]
  by_cases hb : (b : ℕ) < T.pos i + 1 + 1
  · rw [dif_pos hb, if_pos hb]
    by_cases hb2 : (b : ℕ) < T.pos i + 1
    · have : (⟨b, hb⟩ : Fin (T.pos i + 1 + 1)) = Fin.castSucc ⟨b, hb2⟩ := rfl
      rw [this, Formalism.GM.M.FB.snoc_deg_castSucc]
      simp [hLLK, Letters.takeD, b.isLt]
    · have : (⟨b, hb⟩ : Fin (T.pos i + 1 + 1)) = Fin.last _ := by apply Fin.ext; simp; omega
      rw [this, Formalism.GM.M.FB.snoc_deg_last]
      have hb3 : b = ⟨T.pos i + 1, by omega⟩ := by apply Fin.ext; simp; omega
      rw [hb3, setTies_deg_eta LL T hadm i n]
  · rw [dif_neg hb, if_neg hb]; simp

theorem Ffull_ycond [NeZero r] (ρ : Fin r) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (k : Fin T.q) (hk : T.J k ≤ T.pos i + 1) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ YCond p LL (T.J k) (T.thr k) := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have hY : f ∈ Y p LLK T.J (T.thrUpTo i) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hY).1
  let J' : Fin T.q → ℕ := fun k => min (T.J k) (T.pos i + 1)
  have hY' : f ∈ Y p LLK J' (T.thrUpTo i) := by
    refine Submodule.mem_inf.mpr ⟨hP, Submodule.mem_iInf _ |>.mpr fun k' => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hY).2 k'
    by_cases hk' : T.J k' ≤ T.pos i + 1
    · simpa [J', min_eq_left hk'] using this
    · have ht : T.thrUpTo i k' = ⊤ := by simp [TieData.thrUpTo, hk']
      rw [ht, ycond_top]; exact Submodule.mem_top
  have hF := (Formalism.GM.extendWeightBounded p (T.pos i + 1) r LLK ρ (n i) J' (T.thrUpTo i) hS
    (fun k => min_le_right _ _) f hP).mp hY'
  have hF2 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hF).2 k
  have e1 : J' k = T.J k := min_eq_left hk
  have e2 : T.thrUpTo i k = T.thr k := by simp [TieData.thrUpTo, hk]
  rw [e1, e2] at hF2
  rw [Ffull_eq]
  refine Formalism.GM.FrozenVariableComponents.ycond_map p (LLK.snoc (n i)) LL (T.J k) (T.J k) (T.thr k)
    (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap
    (fun c d G => glAct_rename (LLK.snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a) (T.J k) c d G) ?_ _ hF2
  intro G m hm
  rw [AlgHom.toLinearMap_apply, support_rename_of_injective (inclusion_prodMap_injective (r := r) hK), Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  refine ⟨m0, hm0, ?_⟩
  rw [← weight_wv, ← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i)]

theorem Ffull_step (ρ : Fin r) (n : Fin T.t → ℕ) (n' : ℕ) (hn : n i ≤ n')
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T (Function.update n i n')) i ρ n' f =
      X (⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩, ρ) ^ (n' - n i) *
        T.Ffull p (LL.setTies T n) i ρ (n i) f := by
  have hK := hK_of_adm LL T hadm i
  rw [Ffull_eq, Ffull_eq, takeD_update LL T hadm i n n']
  set LLK := (LL.setTies T n).takeD (T.pos i + 1)
  have step : ∀ d : ℕ, freeze p LLK ρ (n i + d) f = X (Fin.last (T.pos i + 1), ρ) ^ d * freeze p LLK ρ (n i) f := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← add_assoc, ← Formalism.GM.extendSucc p (T.pos i + 1) r LLK ρ (n i + d) (by omega) f, ih, pow_succ]
      ring
  rw [show n' = n i + (n' - n i) by omega, step, map_mul, map_pow, rename_X, Nat.add_sub_cancel_left]
  congr 2
  congr 1
  refine Prod.ext (Fin.ext ?_) rfl
  show ((ιF N (T.pos i + 1) (Fin.last (T.pos i + 1)) : Fin N) : ℕ) = T.pos i + 1
  rw [ιF_val hK]; simp

end Tie2

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

theorem comp_mul_hom {σ M K : Type} [AddCommGroup M] [CommRing K] (w : σ → M) {φ : MvPolynomial σ K} {κ : M}
    (hφ : IsWeightedHomogeneous w φ κ) (ν : M) (x : MvPolynomial σ K) :
    weightedHomogeneousComponent w (ν + κ) (φ * x) = φ * weightedHomogeneousComponent w ν x := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff ab.1 φ = 0
    · rw [h0, zero_mul, zero_mul]
    · have h1 : Finsupp.weight w ab.1 = κ := hφ h0
      have hab' : ab.1 + ab.2 = d := by simpa using hab
      have h2 : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w d := by
        rw [← map_add, hab']
      have h3 : Finsupp.weight w ab.2 = ν := by
        rw [h1, hd, add_comm] at h2
        exact add_right_cancel h2
      rw [if_pos h3]
  · symm
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : coeff ab.1 φ = 0
    · rw [h0, zero_mul]
    · have h1 : Finsupp.weight w ab.1 = κ := hφ h0
      have hab' : ab.1 + ab.2 = d := by simpa using hab
      have h2 : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w d := by
        rw [← map_add, hab']
      rw [if_neg, mul_zero]
      intro h3
      apply hd
      rw [← h2, h1, h3, add_comm]

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem weight_cov_monomial (LL : Letters N) (j0 : ℕ) (iK : Fin N) (hiK : (iK : ℕ) < j0) (hv : LL.vec iK = false)
    (m : Fin N × Fin r →₀ ℕ) (hm : ∀ v : Fin N × Fin r, v.1 ≠ iK → m v = 0) :
    Finsupp.weight (wv LL j0) m = fun c => -((m (iK, c) : ℕ) : ℤ) := by
  funext c
  rw [weight_wv]
  unfold wt
  rw [Finset.sum_eq_single iK]
  · simp [hiK, hv]
  · intro b _ hb
    have h0 : m (b, c) = 0 := hm (b, c) hb
    split_ifs <;> simp [h0]
  · simp

theorem cprod_eig {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
    {x : V} {e : ℤ} (hx : G.Cas x = ((e : ℤ) : K) • x) (cs : List ℤ) :
    G.cprod cs x = (cs.map (fun c => (((e - c : ℤ)) : K))).prod • x := by
  induction cs with
  | nil => simp [GlW.cprod]
  | cons c cs ih =>
    rw [G.cprod_cons, ih, map_smul, hx, smul_smul, smul_smul, ← sub_smul, List.map_cons, List.prod_cons]
    congr 1
    push_cast
    ring

theorem cprod_ne {K V : Type} [Field K] [CharZero K] (e : ℤ) (cs : List ℤ) (h : ∀ c ∈ cs, c ≠ e) :
    (cs.map (fun c => (((e - c : ℤ)) : K))).prod ≠ 0 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons]
    refine mul_ne_zero ?_ (ih fun c' hc' => h c' (by simp [hc']))
    have hc : c ≠ e := h c (by simp)
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hc)

theorem Cas_mul_B (LL : Letters N) (j0 : ℕ) (y q : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    (GA p LL j0).Cas (y * q) = (GA p LL j0).Cas y * q := by
  rw [GlW.Cas_apply, GlW.Cas_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  show glAct p LL j0 a b (glAct p LL j0 b a (y * q)) = glAct p LL j0 a b (glAct p LL j0 b a y) * q
  rw [glAct_mul_kill LL j0 b a y hq, glAct_mul_kill LL j0 a b _ hq]

theorem cprod_mul_B (LL : Letters N) (j0 : ℕ) (cs : List ℤ) (y q : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    (GA p LL j0).cprod cs (y * q) = (GA p LL j0).cprod cs y * q := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [GlW.cprod_cons, GlW.cprod_cons, ih, Cas_mul_B LL j0 _ q hq, sub_mul, smul_mul_assoc]

theorem pol_stable (LL L2 : Letters N) (j : ℕ) : (GA p LL j).Stable (Pol p r L2) := fun a b x hx => glAct_pol LL L2 j a b hx

theorem gSpan_eq (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) (j : ℕ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    gSpan p (LL.setTies T n) j F = (GA p LL j).gS {F} := by
  unfold gSpan GlW.gS
  congr 1
  ext S
  simp only [Set.mem_setOf_eq, Set.singleton_subset_iff, SetLike.mem_coe]
  rfl

theorem rep_span (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (j0 : ℕ)
    {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF, ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)},
      x = g * q}) :
    ∃ s : Finset (Fin N × Fin r →₀ ℕ), ∃ a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ b ∈ s, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0) ∧ (∀ b, a b ∈ VF) ∧
        z = ∑ b ∈ s, a b * monomial b 1 := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, q, hq, rfl⟩ := hx
    refine ⟨q.support, fun b => coeff b q • g, ?_, fun b => VF.smul_mem _ hg, ?_⟩
    · intro b hb v hv
      by_contra hne
      have := supp_of_supported hq b hb v hne
      simp only [Set.mem_setOf_eq] at this
      omega
    · conv_lhs => rw [q.as_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_assoc, ← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
  | zero => exact ⟨∅, fun _ => 0, by simp, fun _ => VF.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s1, a1, hs1, ha1, rfl⟩ := hx
    obtain ⟨s2, a2, hs2, ha2, rfl⟩ := hy
    refine ⟨s1 ∪ s2, fun b => (if b ∈ s1 then a1 b else 0) + (if b ∈ s2 then a2 b else 0), ?_, ?_, ?_⟩
    · intro b hb; rcases Finset.mem_union.mp hb with h | h
      · exact hs1 b h
      · exact hs2 b h
    · intro b
      refine VF.add_mem ?_ ?_ <;> split_ifs <;> first | exact ha1 b | exact ha2 b | exact VF.zero_mem
    · simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
  | smul c x _ hx =>
    obtain ⟨s, a, hs, ha, rfl⟩ := hx
    refine ⟨s, fun b => c • a b, hs, fun b => VF.smul_mem c (ha b), ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc]

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem dle_cov (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (u : ℕ) (a : Fin r → ℕ) (ha : ∑ c, a c = u) :
    Dle (fun c => -((a c : ℕ) : ℤ)) (-(u : ℤ) • Pi.single ρ 1) := by
  subst ha
  refine ⟨fun k => ?_, ?_⟩
  · unfold psum
    by_cases hk : (ρ : ℕ) < k
    · have hall : ∀ c : Fin r, (c : ℕ) < k := fun c => by have := c.isLt; omega
      simp only [hall, if_true]
      simp [Pi.single_apply]
    · have h1 : ∑ c : Fin r, (if (c : ℕ) < k then (-((∑ c, a c : ℕ) : ℤ) • Pi.single ρ (1 : ℤ)) c else 0) = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        split_ifs with hc
        · have hcρ : c ≠ ρ := fun h => hk (h ▸ hc)
          simp [Pi.single_apply, hcρ]
        · rfl
      rw [h1]
      exact Finset.sum_nonpos fun c _ => by split_ifs <;> simp
  · simp [Pi.single_apply]

theorem weight_zero_span_highest [NeZero r] (LL : Letters N) (j0 : ℕ) (iK : Fin N) (hiK : (iK : ℕ) < j0)
    (hvK : LL.vec iK = false) (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (la : Fin r → ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : (GA p LL j0).IsHW la F) (u : ℕ) :
    ∀ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p LL j0).gS {F},
        ∃ s ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
          weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)), x = g * s},
      (∀ μ, ¬ Dle μ (la - (u : ℤ) • Pi.single ρ 1) → (GA p LL j0).comp μ x = 0) ∧
      (GA p LL j0).comp (la - (u : ℤ) • Pi.single ρ 1) x ∈ Submodule.span ℚ_[p] {X (iK, ρ) ^ u * F} := by
  classical
  set G := GA p LL j0 with hG
  set la' := la - (u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) with hla'
  let Ωs : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    { carrier := {x | (∀ μ, ¬ Dle μ la' → G.comp μ x = 0) ∧ G.comp la' x ∈ Submodule.span ℚ_[p] {X (iK, ρ) ^ u * F}}
      add_mem' := by
        intro x y hx hy
        exact ⟨fun μ hμ => by rw [map_add, hx.1 μ hμ, hy.1 μ hμ, add_zero], by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩
      zero_mem' := ⟨fun μ _ => map_zero _, by rw [map_zero]; exact Submodule.zero_mem _⟩
      smul_mem' := by
        intro c x hx
        exact ⟨fun μ hμ => by rw [map_smul, hx.1 μ hμ, smul_zero], by rw [map_smul]; exact Submodule.smul_mem _ c hx.2⟩ }
  suffices hsuff : Submodule.span ℚ_[p] {x | ∃ g ∈ G.gS {F}, ∃ s ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
      weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)), x = g * s} ≤ Ωs from
    fun x hx => hsuff hx
  rw [Submodule.span_le]
  rintro _ ⟨g, hg, s, hs, rfl⟩
  obtain ⟨S, hS⟩ := G.dec g
  rw [← G.sum_comp g S hS, Finset.sum_mul]
  refine Ωs.sum_mem fun ν _ => ?_
  conv => arg 2; arg 2; rw [s.as_sum]
  rw [Finset.mul_sum]
  refine Ωs.sum_mem fun m hm => ?_

  have hm1 : ∀ v : Fin N × Fin r, v.1 ≠ iK → m v = 0 := wOut_zero ((Submodule.mem_inf.mp hs).1 (mem_support_iff.mp hm))
  have hm2 : ∑ c, m (iK, c) = u := by
    have := congrFun ((Submodule.mem_inf.mp hs).2 (mem_support_iff.mp hm)) iK
    rw [weight_wL] at this
    simp only [Pi.single_eq_same] at this
    exact_mod_cast this
  set wm : Fin r → ℤ := fun c => -((m (iK, c) : ℕ) : ℤ) with hwm
  have hwmm : Finsupp.weight (wv LL j0) m = wm := weight_cov_monomial LL j0 iK hiK hvK m hm1
  have hy : G.comp ν g * monomial m (coeff m s) ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL j0) (ν + wm) := by
    have := (weightedHomogeneousComponent_isWeightedHomogeneous (w := wv LL j0) ν g).mul
      (isWeightedHomogeneous_monomial (wv LL j0) m (coeff m s) hwmm)
    exact this
  have hcomp : ∀ μ, G.comp μ (G.comp ν g * monomial m (coeff m s)) =
      if μ = ν + wm then G.comp ν g * monomial m (coeff m s) else 0 := fun μ =>
    weightedHomogeneousComponent_of_mem hy
  by_cases h0 : G.comp ν g = 0
  · rw [h0, zero_mul]; exact Ωs.zero_mem
  have hgν : G.comp ν g ∈ G.gS {F} := G.graded_of (G.gS_stable _) ν g hg
  have hν : Dle ν la := G.wt_le_of_mem hF hgν (by rw [G.idem, if_pos rfl]; exact h0)
  have hle : Dle (ν + wm) la' := by
    refine Dle_trans (Dle_add_right hν wm) ?_
    have h1 := Dle_add_right (dle_cov ρ hρ u (fun c => m (iK, c)) hm2) la
    rw [hla', sub_eq_add_neg, ← neg_smul]
    simpa [add_comm] using h1
  refine ⟨fun μ hμ => ?_, ?_⟩
  · rw [hcomp, if_neg]; rintro rfl; exact hμ hle
  · rw [hcomp]
    split_ifs with heq
    ·
      have hν' : ν = la' - wm := eq_sub_of_add_eq heq.symm
      have hps := hν.1 (r - 1)
      rw [hν', hla', psum_sub, psum_sub] at hps
      have hp0 : psum ((u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) (r - 1) = 0 := by
        unfold psum
        refine Finset.sum_eq_zero fun c _ => ?_
        split_ifs with h
        · have : c ≠ ρ := fun h' => by subst h'; omega
          simp [Pi.single_apply, this]
        · rfl
      have hpw : psum wm (r - 1) = -∑ c : Fin r, (if (c : ℕ) < r - 1 then ((m (iK, c) : ℕ) : ℤ) else 0) := by
        unfold psum; rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp [hwm]
      rw [hp0, hpw] at hps
      have hnn : ∀ c ∈ (Finset.univ : Finset (Fin r)), (0 : ℤ) ≤ (if (c : ℕ) < r - 1 then ((m (iK, c) : ℕ) : ℤ) else 0) := by
        intro c _; split_ifs <;> simp
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by linarith [Finset.sum_nonneg hnn])
      have hmc : ∀ c, c ≠ ρ → m (iK, c) = 0 := by
        intro c hc
        have hlt : (c : ℕ) < r - 1 := by
          have := c.isLt
          have : (c : ℕ) ≠ ρ := fun h => hc (Fin.ext h)
          omega
        have := hz c (Finset.mem_univ c)
        rw [if_pos hlt] at this
        exact_mod_cast this
      have hmρ : m (iK, ρ) = u := by
        rw [← hm2, Finset.sum_eq_single ρ (fun c _ hc => hmc c hc) (by simp)]
      have hmeq : m = Finsupp.single (iK, ρ) u := by
        ext v
        by_cases hv1 : v.1 = iK
        · by_cases hv2 : v.2 = ρ
          · have : v = (iK, ρ) := Prod.ext hv1 hv2
            subst this; rw [Finsupp.single_eq_same, hmρ]
          · have : v = (iK, v.2) := Prod.ext hv1 rfl
            rw [this, hmc v.2 hv2, Finsupp.single_eq_of_ne]
            intro h; exact hv2 (Prod.mk.inj h).2
        · rw [hm1 v hv1, Finsupp.single_eq_of_ne]
          intro h; exact hv1 (Prod.mk.inj h).1
      have hwmρ : wm = -((u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) := by
        funext c
        simp only [hwm, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hc : c = ρ
        · subst hc; simp [hmρ]
        · simp [hmc c hc, hc]
      have hνla : ν = la := by rw [hν', hwmρ, hla']; abel
      obtain ⟨c', hc'⟩ := G.comp_top_of_mem hF hg
      have hmono : monomial m (coeff m s) = coeff m s • (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p]) := by
        rw [hmeq, X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]
      rw [hνla, hc', hmono, smul_mul_smul_comm, mul_comm F]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · exact Submodule.zero_mem _

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem setTies_deg_ne (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ)
    (n' : ℕ) (b : Fin N) (hb : (b : ℕ) ≠ T.pos i + 1) :
    (LL.setTies T (Function.update n i n')).deg b = (LL.setTies T n).deg b := by
  simp only [Letters.setTies]
  split_ifs with h
  · have hne : Classical.choose h ≠ i := by
      intro he
      have := Classical.choose_spec h
      rw [he] at this; omega
    rw [Function.update_of_ne hne]
  · rfl

theorem eta_wL (iK : Fin N) (ρ : Fin r) (u : ℕ) :
    IsWeightedHomogeneous (wL N r) (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p]) (Pi.single iK (u : ℤ)) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
  funext i
  simp [wL, Pi.single_apply]

theorem eta_wOut (iK : Fin N) (ρ : Fin r) (u : ℕ) :
    IsWeightedHomogeneous (wOut N r iK) (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p]) 0 := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
  simp [wOut]

theorem eta_wv (LL : Letters N) (j0 : ℕ) (iK : Fin N) (hiK : (iK : ℕ) < j0) (hv : LL.vec iK = false)
    (ρ : Fin r) (u : ℕ) :
    IsWeightedHomogeneous (wv LL j0) (X (iK, ρ) ^ u : MvPolynomial (Fin N × Fin r) ℚ_[p])
      (-(u : ℤ) • Pi.single ρ 1) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
  funext c
  simp [wv, hiK, hv, Pi.single_apply] <;> split_ifs <;> simp

theorem pol_eta (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ)
    (n' : ℕ) (hn : n i ≤ n') (ρ : Fin r)
    {z : MvPolynomial (Fin N × Fin r) ℚ_[p]} (L0 L1 : Letters N)
    (h0 : ∀ b : Fin N, (b : ℕ) ≠ T.pos i + 1 → L1.deg b = L0.deg b)
    (h1 : ∀ b : Fin N, (b : ℕ) = T.pos i + 1 → L0.deg b = n i ∧ L1.deg b = n')
    (hz : z ∈ Pol p r L0) :
    X (⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩, ρ) ^ (n' - n i) * z ∈ Pol p r L1 := by
  rw [pol_iff] at hz ⊢
  have := (eta_wL (p := p) (r := r) ⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩ ρ (n' - n i)).mul hz
  convert this using 1
  funext b
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hb : (b : ℕ) = T.pos i + 1
  · have hb' : b = ⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩ := Fin.ext hb
    rw [if_pos hb', (h1 b hb).1, (h1 b hb).2]; push_cast [Nat.cast_sub hn]; ring
  · have hb' : b ≠ ⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩ := fun h => hb (by rw [h])
    rw [if_neg hb', h0 b hb, zero_add]

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM.DimensionMonotonicity

open MvPolynomial Finset Formalism.GM.M

theorem highest_weight_dim_monotone : WeightSpaceDimMonotone := by
  intro p _ N r _ _ LL T hadm ρ hρ hr i n w f hf hf0 hS n' hn
  classical
  have hK := hK_of_adm LL T hadm i
  have hiKN : T.pos i + 1 < N := by omega
  set nU := Function.update n i n' with hnU
  set G := GA p LL (T.pos i + 1 + 1) with hG
  set iK : Fin N := ⟨T.pos i + 1, hiKN⟩ with hiK
  set u := n' - n i with hu
  set eta : MvPolynomial (Fin N × Fin r) ℚ_[p] := X (iK, ρ) ^ u with heta
  set F := T.Ffull p (LL.setTies T n) i ρ (n i) f with hFdef
  set F' := T.Ffull p (LL.setTies T nU) i ρ n' f with hF'def
  set la := w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) with hla
  set la' := w - ((n' : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) with hla'
  have hvK : LL.vec iK = false := vec_eta LL T hadm i hiKN
  have hiKlt : (iK : ℕ) < T.pos i + 1 + 1 := by simp [hiK]
  have hρa : ∀ a b : Fin r, a < b → a ≠ ρ := by
    intro a b hab h; subst h
    have : (a : ℕ) < b := hab
    have := b.isLt; omega

  have hfU : f ∈ MMw p ((LL.setTies T nU).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w := by
    rw [hnU, takeD_update LL T hadm i n n']; exact hf
  have hSU : ((LL.setTies T nU).takeD (T.pos i + 1)).total ≤ nU i := by
    rw [hnU, takeD_update LL T hadm i n n', Function.update_self]; omega
  have hnUi : nU i = n' := by rw [hnU, Function.update_self]
  have hFhw : G.IsHW la F := Ffull_hw LL T hadm i ρ hρ n w f hf hS
  have hF'hw : G.IsHW la' F' := by
    have := Ffull_hw LL T hadm i ρ hρ nU w f hfU hSU
    rw [hnUi] at this; exact this
  have hF0 : F ≠ 0 := Ffull_ne LL T hadm i ρ n w f hf hf0 hS
  have hF'0 : F' ≠ 0 := by
    have := Ffull_ne LL T hadm i ρ nU w f hfU hf0 hSU
    rw [hnUi] at this; exact this
  have hstep : F' = eta * F := Ffull_step LL T hadm i ρ n n' hn f hS
  have hfP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)) :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1).1
  have hlala : la' = la - (u : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) := by
    rw [hla', hla, hu, Nat.cast_sub hn]; rw [sub_smul]; abel

  set L0 := Lz (LL.setTies T n) (T.pos i + 1 + 1) with hL0
  set L1 := Lz (LL.setTies T nU) (T.pos i + 1 + 1) with hL1
  have hFpol : F ∈ Pol p r L0 := Ffull_pol LL T hadm i ρ n f hfP hS
  have hVF : G.gS {F} ≤ Pol p r L0 := G.gS_le (by simpa using hFpol) (pol_stable LL L0 _)
  have hL01a : ∀ b : Fin N, (b : ℕ) ≠ T.pos i + 1 → L1.deg b = L0.deg b := by
    intro b hb
    simp only [hL0, hL1, Lz]
    split_ifs
    · exact setTies_deg_ne LL T hadm i n n' b hb
    · rfl
  have hL01b : ∀ b : Fin N, (b : ℕ) = T.pos i + 1 → L0.deg b = n i ∧ L1.deg b = n' := by
    intro b hb
    have hb' : b = iK := Fin.ext hb
    subst hb'
    simp only [hL0, hL1, Lz, hiKlt, if_true]
    exact ⟨setTies_deg_eta LL T hadm i n hiKN, by rw [setTies_deg_eta LL T hadm i nU hiKN, hnUi]⟩

  set Hu := weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
    weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)) with hHu
  set W0 := Submodule.span ℚ_[p] {x | ∃ g ∈ G.gS {F}, ∃ s ∈ Hu, x = g * s} with hW0
  have hetaHu : eta ∈ Hu := Submodule.mem_inf.mpr ⟨eta_wOut iK ρ u, eta_wL iK ρ u⟩
  have hHu_st : ∀ a b, ∀ s ∈ Hu, glAct p LL (T.pos i + 1 + 1) a b s ∈ Hu := by
    intro a b s hs
    exact Submodule.mem_inf.mpr ⟨glAct_lw LL _ a b _ (fun _ _ _ => rfl) (Submodule.mem_inf.mp hs).1,
      glAct_lw LL _ a b _ (fun _ _ _ => rfl) (Submodule.mem_inf.mp hs).2⟩
  have hW0st : G.Stable W0 := by
    intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, s, hs, rfl⟩ := hx
      show glAct p LL (T.pos i + 1 + 1) a b (g * s) ∈ W0
      rw [Formalism.GM.M.FB.glAct_mul]
      refine W0.add_mem (Submodule.subset_span ⟨g, hg, _, hHu_st a b s hs, rfl⟩) ?_
      rw [mul_comm]
      exact Submodule.subset_span ⟨_, G.gS_stable _ a b g hg, s, hs, rfl⟩
    | zero => rw [map_zero]; exact W0.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W0.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W0.smul_mem c hx
  have hW0pol : W0 ≤ Pol p r L1 := by
    rw [hW0, Submodule.span_le]
    rintro _ ⟨g, hg, s, hs, rfl⟩
    rw [mul_comm]
    have hgp := hVF hg
    rw [SetLike.mem_coe, pol_iff]
    rw [pol_iff] at hgp
    have := ((Submodule.mem_inf.mp hs).2).mul hgp
    convert this using 1
    funext b
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hb : (b : ℕ) = T.pos i + 1
    · have hb' : b = iK := Fin.ext hb
      rw [if_pos hb', (hL01b b hb).1, (hL01b b hb).2, hu]; push_cast [Nat.cast_sub hn]; ring
    · have hb' : b ≠ iK := fun h => hb (by rw [h])
      rw [if_neg hb', hL01a b hb, zero_add]
  haveI : FiniteDimensional ℚ_[p] (Pol p r L1) := pol_fd L1
  haveI hW0fd : FiniteDimensional ℚ_[p] W0 := Submodule.finiteDimensional_of_le hW0pol
  have hW0f : G.FinW W0 := by
    obtain ⟨S, hS'⟩ := pol_finW (p := p) (r := r) L1 (T.pos i + 1 + 1)
    exact ⟨S, fun x hx => hS' x (hW0pol hx)⟩
  have hF'W0 : F' ∈ W0 := by
    rw [hstep, mul_comm]; exact Submodule.subset_span ⟨F, G.subset_gS _ (Set.mem_singleton F), eta, hetaHu, rfl⟩
  have hVF'W0 : G.gS {F'} ≤ W0 := G.gS_le (by simpa using hF'W0) hW0st
  have hwts := weight_zero_span_highest LL (T.pos i + 1 + 1) iK hiKlt hvK ρ hρ la F hFhw u
  rw [← hlala, ← hstep] at hwts

  obtain ⟨cs, hcs, hP⟩ := G.chain (W := W0) (V0 := G.gS {F'}) hW0st hW0f (G.gS_stable _) hVF'W0 (GlW.casI la') (by
    intro U hU hVU hUW μ v hvW hvU hvw hr hc
    have hdμ := G.dom_of_hwmod hU hW0st hW0f hvW hvU hvw hr
    have hdla' := G.dom_of_hwmod G.bot_stable hW0st hW0f hF'W0 (by rwa [Submodule.mem_bot]) hF'hw.1
      (fun a b h => by rw [hF'hw.2 a b h]; exact Submodule.zero_mem _)
    have hv0 : v ≠ 0 := fun h => hvU (h ▸ U.zero_mem)
    have hle : Dle μ la' := by
      by_contra hn'
      apply hv0; rw [← hvw]; exact (hwts v hvW).1 μ hn'
    by_cases hμ : μ = la'
    · subst hμ
      apply hvU
      have h2 := (hwts v hvW).2
      rw [hvw] at h2
      exact hVU ((Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (G.subset_gS _ (Set.mem_singleton F')))) h2)
    · exact absurd hc (ne_of_lt (cas_lt hdμ hdla' hle hμ)))
  set P := G.cprod cs with hPdef
  have hCasF' : G.Cas F' = ((GlW.casI la' : ℤ) : ℚ_[p]) • F' := G.Cas_gS hF'hw (G.subset_gS _ (Set.mem_singleton F'))
  have hPF' : P F' = (cs.map (fun c => (((GlW.casI la' - c : ℤ)) : ℚ_[p]))).prod • F' := cprod_eig G hCasF' cs
  have hκ : (cs.map (fun c => (((GlW.casI la' - c : ℤ)) : ℚ_[p]))).prod ≠ 0 := cprod_ne (V := ℚ_[p]) _ cs hcs
  set Φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
    P ∘ₗ LinearMap.mulLeft ℚ_[p] eta with hΦdef
  have hΦapp : ∀ x, Φ x = P (eta * x) := fun x => rfl
  have hEeta : ∀ a b : Fin r, a < b → glAct p LL (T.pos i + 1 + 1) a b eta = 0 := by
    intro a b hab
    apply glAct_pow_zero
    rw [glAct_X_gen, if_pos hiKlt, hvK]
    simp [Ne.symm (hρa a b hab)]
  have hΦE : ∀ x ∈ G.gS {F}, ∀ a b, a < b → Φ (G.E a b x) = G.E a b (Φ x) := by
    intro x _ a b hab
    rw [hΦapp, hΦapp, G.E_cprod]
    congr 1
    show eta * glAct p LL (T.pos i + 1 + 1) a b x = glAct p LL (T.pos i + 1 + 1) a b (eta * x)
    rw [Formalism.GM.M.FB.glAct_mul, hEeta a b hab, mul_zero, add_zero]
  have hetawv := eta_wv (p := p) LL (T.pos i + 1 + 1) iK hiKlt hvK ρ u
  have hΦc : ∀ x ∈ G.gS {F}, ∀ ν, Φ (G.comp ν x) = G.comp (ν + (-(u : ℤ) • Pi.single ρ 1)) (Φ x) := by
    intro x _ ν
    rw [hΦapp, hΦapp, G.comp_cprod]
    congr 1
    exact (comp_mul_hom (wv LL _) hetawv ν x).symm
  have hΦv : Φ F ≠ 0 := by rw [hΦapp, ← hstep, hPF']; exact smul_ne_zero hκ hF'0
  have hinjF := G.inj_of hFhw (pol_stable LL L0 _) (pol_finW L0 _) hFpol Φ _ hΦE hΦc hΦv
  have hΦg : ∀ g ∈ G.gS {F}, Φ g ∈ G.gS {F'} := by
    intro g hg
    rw [hΦapp]
    apply hP
    rw [mul_comm]; exact Submodule.subset_span ⟨g, hg, eta, hetaHu, rfl⟩
  have hΦB : ∀ y q : MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < T.pos i + 1 + 1 → m v = 0) → Φ (y * q) = Φ y * q := by
    intro y q hq
    rw [hΦapp, hΦapp, ← mul_assoc]
    exact cprod_mul_B LL _ cs _ q hq
  have hBsupp : ∀ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)},
      ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < T.pos i + 1 + 1 → m v = 0 := by
    intro q hq m hm v hv
    by_contra hne
    have := supp_of_supported hq m hm v hne
    simp only [Set.mem_setOf_eq] at this
    omega
  have hspan : ∀ z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T n) (T.pos i + 2) F,
        ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q},
      Φ z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T nU) (T.pos i + 2)
        (T.Ffull p (LL.setTies T nU) i ρ (nU i) f),
        ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q} := by
    intro z hz
    rw [hnUi]
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, q, hq, rfl⟩ := hx
      rw [hΦB g q (hBsupp q hq)]
      refine Submodule.subset_span ⟨Φ g, ?_, q, hq, rfl⟩
      rw [gSpan_eq]; rw [gSpan_eq] at hg; exact hΦg g hg
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hmaps : ∀ z ∈ T.YYsp p LL i ρ n f, Φ z ∈ T.YYsp p LL i ρ nU f := by
    intro z hz
    obtain ⟨hzY, hzS⟩ := Submodule.mem_inf.mp hz
    have hzS' := hspan z hzS
    refine Submodule.mem_inf.mpr ⟨?_, hzS'⟩
    obtain ⟨hzP, hzC⟩ := Submodule.mem_inf.mp hzY
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hΦapp]
      refine G.cprod_mem (pol_stable LL _ _) cs ?_
      exact pol_eta LL T hadm i n n' hn ρ (LL.setTies T n) (LL.setTies T nU)
        (fun b hb => setTies_deg_ne LL T hadm i n n' b hb)
        (fun b hb => by
          have hb' : b = iK := Fin.ext hb
          subst hb'
          exact ⟨setTies_deg_eta LL T hadm i n hiKN, by rw [setTies_deg_eta LL T hadm i nU hiKN, hnUi]⟩) hzP
    · rw [Submodule.mem_iInf]; intro k
      have hzk : z ∈ YCond p LL (T.J k) (T.thr k) := (Submodule.mem_iInf _).mp hzC k
      show Φ z ∈ YCond p LL (T.J k) (T.thr k)
      by_cases hk : T.J k ≤ T.pos i + 1
      · have hF'Y : F' ∈ YCond p LL (T.J k) (T.thr k) := by
          have := Ffull_ycond LL T hadm i ρ nU w f hfU hSU k hk
          rw [hnUi] at this; exact this
        have hle : Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T nU) (T.pos i + 2)
            (T.Ffull p (LL.setTies T nU) i ρ (nU i) f),
            ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q} ≤
            YCond p LL (T.J k) (T.thr k) := by
          rw [Submodule.span_le]
          rintro _ ⟨g, hg, q, hq, rfl⟩
          rw [hnUi, gSpan_eq] at hg
          have hgY : g ∈ YCond p LL (T.J k) (T.thr k) :=
            (G.gS_le (by simpa using hF'Y) (fun a b x hx => ycond_glAct_le LL (by omega : T.J k ≤ T.pos i + 1 + 1) _ a b hx)) hg
          rw [SetLike.mem_coe, mul_comm]
          exact ycond_mul_B LL (by omega : T.J k ≤ T.pos i + 1 + 1) _ (hBsupp q hq) g hgY
        exact hle hzS'
      · push Not at hk
        rw [hΦapp]
        refine ycond_cprod LL (by omega : T.pos i + 1 + 1 ≤ T.J k) _ cs ?_
        exact ycond_mul_cov LL (T.J k) (T.thr k) iK (by simp only [hiK]; omega) hvK (eta_wOut iK ρ u) z hzk
  have hinjY : ∀ z ∈ T.YYsp p LL i ρ n f, Φ z = 0 → z = 0 := by
    intro z hz h0
    have hzS := (Submodule.mem_inf.mp hz).2
    simp only [gSpan_eq] at hzS
    obtain ⟨s, a, hs, ha, rfl⟩ := rep_span (G.gS {F}) (T.pos i + 1 + 1) hzS
    have hsum : ∑ b ∈ s, Φ (a b) * monomial b 1 = 0 := by
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [hΦB _ _ ?_]
      intro m hm v hv
      rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
      subst hm; exact hs _ hb v hv
    have hA : ∀ b ∈ s, ∀ m ∈ (Φ (a b)).support, ∀ v : Fin N × Fin r, T.pos i + 1 + 1 ≤ (v.1 : ℕ) → m v = 0 := by
      intro b _ m hm v hv
      have hp := hW0pol (hVF'W0 (hΦg (a b) (ha b)))
      have h1 := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hp hm v.1
      have h2 : L1.deg v.1 = 0 := by simp only [hL1, Lz]; rw [if_neg (by omega)]
      rw [h2] at h1
      exact (Finset.sum_eq_zero_iff.mp h1) v.2 (Finset.mem_univ _)
    have hz0 := indep_B (T.pos i + 1 + 1) s (fun b => Φ (a b)) hs hA hsum
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [hinjF (a b) (ha b) (hz0 b hb), zero_mul]
  haveI : FiniteDimensional ℚ_[p] (Pol p r (LL.setTies T nU)) := pol_fd _
  haveI : FiniteDimensional ℚ_[p] (T.YYsp p LL i ρ nU f) :=
    Submodule.finiteDimensional_of_le (le_trans inf_le_left inf_le_left)
  let Φ' : (T.YYsp p LL i ρ n f) →ₗ[ℚ_[p]] (T.YYsp p LL i ρ nU f) :=
    (Φ.domRestrict _).codRestrict _ (fun z => hmaps z z.2)
  apply LinearMap.finrank_le_finrank_of_injective (f := Φ')
  intro z1 z2 h12
  have h3 : Φ (z1 - z2) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr (congrArg Subtype.val h12)
  have := hinjY _ (Submodule.sub_mem _ z1.2 z2.2) h3
  exact Subtype.ext (sub_eq_zero.mp this)

end Formalism.GM.DimensionMonotonicity

namespace Formalism.GM

theorem weight_space_dimension_monotone : M.WeightSpaceDimMonotone := DimensionMonotonicity.highest_weight_dim_monotone

end Formalism.GM

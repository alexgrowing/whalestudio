import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

namespace GlobalTheory.CompanionTheory.WordProd.Intl

def consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin (m + 1) ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ)) (by
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ b => simp [Fin.succ_pos]
      | succ a =>
        induction b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ b => simpa using hab)

def shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin m ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono (fun a => (σ a).succ) (fun a b h => by simpa using h)

@[simp] theorem consEmb_zero {m k : ℕ} (σ : Fin m ↪o Fin k) : consEmb σ 0 = 0 := by
  first
    | rfl
    | exact Fin.cons_zero (α := fun _ => Fin (k + 1)) _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) 0 = 0; simp)

@[simp] theorem consEmb_succ {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    consEmb σ a.succ = (σ a).succ := by
  first
    | rfl
    | exact Fin.cons_succ (α := fun _ => Fin (k + 1)) _ _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) a.succ = (σ a).succ; simp)

@[simp] theorem shiftEmb_apply {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    shiftEmb σ a = (σ a).succ := rfl

theorem zero_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) :
    (0 : Fin (k + 1)) ∈ Set.range (consEmb σ) := ⟨0, consEmb_zero σ⟩

theorem succ_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (consEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    cases a using Fin.cases with
    | zero =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero] at ha
      exact absurd ha.symm (Fin.succ_ne_zero j)
    | succ a =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] at ha
      exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.succ, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ σ a⟩

theorem succ_mem_range_shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (shiftEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at ha
    exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply σ a⟩

theorem interleave_embeddings : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w →
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length)
      (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
      (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  intro T u v w h
  induction h with
  | nil =>
    refine ⟨fun j => Fin.elim0 j, (OrderIso.refl _).toOrderEmbedding,
      (OrderIso.refl _).toOrderEmbedding, ?_, ?_, ?_, ?_⟩ <;> intro j <;> exact Fin.elim0 j
  | @left a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (0 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₀
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h1 j
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := u.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hu x
          | simpa using hu x
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hv x
        | simpa using hv x
  | @right a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (1 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₁
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h1 j
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hu x
        | simpa using hu x
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := v.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hv x
          | simpa using hv x

end GlobalTheory.CompanionTheory.WordProd.Intl

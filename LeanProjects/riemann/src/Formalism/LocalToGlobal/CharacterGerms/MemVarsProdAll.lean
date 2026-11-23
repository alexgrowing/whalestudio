import Formalism.LocalToGlobal.CharacterGerms.Interface

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

abbrev Knd (d : ℕ) := Option (Fin 2 × ZMod d × ZMod d)

section Place

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

def kindAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (kind : ∀ i, Fin (what₂ i) → Knd d) (ρ : Fin N) : Knd d :=
  if h : ∃ s, pl s = ρ then kind h.choose.1 h.choose.2 else none

def grAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (ρ : Fin N) :
    MvPowerSeries (WV I) C :=
  if h : ∃ s, pl s = ρ then gr h.choose.1 h.choose.2 else 1

def prodAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) :
    MvPolynomial (Fin N × WV I) C :=
  ∏ i, MvPolynomial.rename (fun x : Fin (what₂ i) × WV I => (pl ⟨i, x.1⟩, x.2)) (P i)

theorem kindAll_pl {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (kind : ∀ i, Fin (what₂ i) → Knd d) (s : Σ i : Fin K, Fin (what₂ i)) : kindAll pl kind (pl s) = kind s.1 s.2 := by
  unfold kindAll
  have hex : ∃ s', pl s' = pl s := ⟨s, rfl⟩
  rw [dif_pos hex]
  have hc : hex.choose = s := hpl hex.choose_spec
  rw [hc]

theorem mem_vars_prodAll {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} {P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C}
    {ρ : Fin N} {w : WV I} (h : (ρ, w) ∈ (prodAll pl P).vars) :
    ∃ s : Σ i : Fin K, Fin (what₂ i), pl s = ρ ∧ (s.2, w) ∈ (P s.1).vars := by
  unfold prodAll at h
  have h1 := MvPolynomial.vars_prod _ h
  rw [Finset.mem_biUnion] at h1
  obtain ⟨i, -, hi⟩ := h1
  have h2 := MvPolynomial.vars_rename _ _ hi
  rw [Finset.mem_image] at h2
  obtain ⟨⟨r, w'⟩, hw', heq⟩ := h2
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨⟨i, r⟩, rfl, hw'⟩

end Place

section Rows

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}

private lemma forall_support_ne_zero_iff_forall_mem_vars {R0 : Type} [Field R0] {α β : Type} (Q : MvPolynomial (α × β) R0)
    (ρ : α) (T : β → Prop) :
    (∀ μ ∈ Q.support, ∀ w, μ (ρ, w) ≠ 0 → T w) ↔ (∀ w, (ρ, w) ∈ Q.vars → T w) := by
  constructor
  · intro H w hw
    obtain ⟨μ, hμ, hx⟩ := (MvPolynomial.mem_vars _).1 hw
    exact H μ hμ w (Finsupp.mem_support_iff.1 hx)
  · intro H μ hμ w hx
    exact H w ((MvPolynomial.mem_vars _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hx⟩)

theorem rowsOK_iff (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ} (P : MvPolynomial (Fin N × WV I) C)
    (kind : Fin N → Knd d) : RowsOK G alt P kind ↔
      (∀ ρ g a a', kind ρ = some (g, a, a') → alt ∧ Odd (a' - a).val ∧
        ∀ w, (ρ, w) ∈ P.vars → OnLeafV G g a a' w) ∧
      (∀ ρ, kind ρ = none → ∃ g : Fin 2, ∀ w : WV I, (ρ, w) ∈ P.vars → w.1 = g) := by
  unfold RowsOK
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).1 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).1 hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).2 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).2 hg⟩

theorem rowsOK_prodAll (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop)
    {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
    (h : ∀ i, RowsOK G alt (P i) (kind i)) : RowsOK G alt (prodAll pl P) (kindAll pl kind) := by
  rw [rowsOK_iff]
  have h' := fun i => (rowsOK_iff G alt (P i) (kind i)).1 (h i)
  refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨h1, h2, h3⟩ := (h' s.1).1 s.2 g a a' hk
      refine ⟨h1, h2, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact h3 w hw'
    · exfalso
      unfold kindAll at hk
      rw [dif_neg hex] at hk
      cases hk
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨g, hg⟩ := (h' s.1).2 s.2 hk
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact hg w hw'
    · refine ⟨0, fun w hw => ?_⟩
      obtain ⟨s', hs', -⟩ := mem_vars_prodAll hw
      exact absurd ⟨s', hs'⟩ hex

end Rows

def JetProdSt : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)]
    (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (N K : ℕ) (what₂ : Fin K → ℕ)
    (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N), Function.Injective pl →
    ∀ (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
      (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C),
      ValOf hL (prodAll pl P) (kindAll pl kind) (grAll pl gr) = ∏ i, ValOf hL (P i) (kind i) (gr i)

end Formalism.L2.FormalSeriesBounds

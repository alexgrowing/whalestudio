import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FiltLevi

section General

variable {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
  {ρ : Representation ℂ G V} {τ : Representation ℂ G Y}

theorem vanish_of_separated (S T : Subrepresentation ρ) {z : G} {c c' : ℂ} (hcc : c ≠ c')
    (hτ : ∀ y, τ z y = c • y) (hS : ∀ y, subQuot S T z y = c' • y) (f : V →ₗ[ℂ] Y)
    (hf : ∀ v, f (ρ z v) = τ z (f v)) (h0 : ∀ v ∈ T.toSubmodule, f v = 0) :
    ∀ v ∈ S.toSubmodule, f v = 0 := by
  intro x hx
  have h := hS (Submodule.Quotient.mk ⟨x, hx⟩)
  change Submodule.Quotient.mk (⟨ρ z x, S.apply_mem_toSubmodule z hx⟩ : S.toSubmodule) =
    c' • Submodule.Quotient.mk (⟨x, hx⟩ : S.toSubmodule) at h
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap] at h
  have h1 := h0 _ h
  simp only [map_sub, map_smul, Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_smul] at h1
  rw [hf, hτ, ← sub_smul] at h1
  exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hcc)

theorem vanish_up (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ) (f : V →ₗ[ℂ] Y)
    (hf : ∀ g v, f (ρ g v) = τ g (f v)) (a b : ℕ)
    (hsep : ∀ t : Fin N, a ≤ t.val → t.val < b →
      ∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y)
    (h0 : ∀ i : Fin (N + 1), i.val = a → ∀ v ∈ (S i).toSubmodule, f v = 0) :
    ∀ n : ℕ, ∀ i : Fin (N + 1), i.val = a + n → i.val ≤ b → ∀ v ∈ (S i).toSubmodule, f v = 0 := by
  intro n
  induction n with
  | zero => intro i hi _; exact h0 i (by simpa using hi)
  | succ n ih =>
    intro i hi hib
    have hiN := i.isLt
    let t : Fin N := ⟨a + n, by omega⟩
    have hts : t.succ = i := Fin.ext (by simp [t, hi]; omega)
    obtain ⟨z, c, c', hcc, hτ, hS⟩ := hsep t (by simp [t]) (by simp [t]; omega)
    rw [← hts]
    exact vanish_of_separated _ _ hcc hτ hS f (hf z) (ih t.castSucc (by simp [t]) (by simp [t]; omega))

def descend (S T : Subrepresentation ρ) (f : ρ.IntertwiningMap τ) (hf : ∀ v ∈ T.toSubmodule, f v = 0) :
    (subQuot S T).IntertwiningMap τ where
  toLinearMap := (T.toSubmodule.comap S.toSubmodule.subtype).liftQ (f.toLinearMap ∘ₗ S.toSubmodule.subtype)
    (fun x hx => by
      rw [LinearMap.mem_ker]
      exact hf _ hx)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext x
    exact f.isIntertwining ρ τ g x

end General

end GlobalTheory.FiltLevi

namespace GlobalTheory.FiltLevi

theorem homLeOne_of_filtration : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
    (∀ t t' : Fin N, t ≠ t' →
      (∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y) ∨
      (∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t'.succ) (S t'.castSucc) z y = c' • y)) →
    (∀ t : Fin N, HomLeOne (subQuot (S t.succ) (S t.castSucc)) τ) → HomLeOne ρ τ := by
  intro G V Y _ _ _ _ _ ρ τ N S _ hbot htop hsep hone μ μ'
  have hbase : ∀ i : Fin (N + 1), i.val = 0 → ∀ v ∈ (S i).toSubmodule, (μ.toLinearMap : V →ₗ[ℂ] Y) v = 0 ∧
      (μ'.toLinearMap : V →ₗ[ℂ] Y) v = 0 := by
    intro i hi v hv
    have hi0 : i = 0 := Fin.ext hi
    rw [hi0, hbot] at hv
    have : v = 0 := (Submodule.mem_bot ℂ).1 hv
    simp [this]
  have hint : ∀ (φ : ρ.IntertwiningMap τ) g v, φ.toLinearMap (ρ g v) = τ g (φ.toLinearMap v) :=
    fun φ g v => φ.isIntertwining ρ τ g v

  have hall : ∀ f : V →ₗ[ℂ] Y, (∀ v ∈ (S (Fin.last N)).toSubmodule, f v = 0) → f = 0 := by
    intro f hf
    ext v
    exact hf v (by rw [htop]; trivial)
  by_cases hs : ∀ t : Fin N,
      ∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y
  · left
    apply hall
    exact vanish_up N S μ.toLinearMap (hint μ) 0 N (fun t _ _ => hs t)
      (fun i hi v hv => (hbase i hi v hv).1) N (Fin.last N) (by simp) le_rfl
  · obtain ⟨t₀, ht₀⟩ := not_forall.1 hs
    have hoth : ∀ t : Fin N, t ≠ t₀ →
        ∃ (z : G) (c c' : ℂ), c ≠ c' ∧ (∀ y, τ z y = c • y) ∧ ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y := by
      intro t ht
      rcases hsep t t₀ ht with h | h
      · exact h
      · exact absurd h ht₀
    have hbelow : ∀ (f : V →ₗ[ℂ] Y), (∀ g v, f (ρ g v) = τ g (f v)) →
        (∀ i : Fin (N + 1), i.val = 0 → ∀ v ∈ (S i).toSubmodule, f v = 0) →
        ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0 := fun f hf h0 =>
      vanish_up N S f hf 0 t₀.val (fun t _ ht => hoth t (fun h => by rw [h] at ht; exact lt_irrefl _ ht)) h0
        t₀.val t₀.castSucc (by simp) (by simp)
    have habove : ∀ (f : V →ₗ[ℂ] Y), (∀ g v, f (ρ g v) = τ g (f v)) →
        (∀ v ∈ (S t₀.succ).toSubmodule, f v = 0) → f = 0 := by
      intro f hf h1
      apply hall
      have := t₀.isLt
      exact vanish_up N S f hf (t₀.val + 1) N
        (fun t ht _ => hoth t (fun h => by rw [h] at ht; omega))
        (fun i hi => by rw [show i = t₀.succ from Fin.ext (by simp [hi])]; exact h1)
        (N - (t₀.val + 1)) (Fin.last N) (by simp <;> omega) le_rfl
    have hμ := hbelow μ.toLinearMap (hint μ) (fun i hi v hv => (hbase i hi v hv).1)
    have hμ' := hbelow μ'.toLinearMap (hint μ') (fun i hi v hv => (hbase i hi v hv).2)
    rcases hone t₀ (descend _ _ μ hμ) (descend _ _ μ' hμ') with h | ⟨c, hc⟩
    · left
      refine habove _ (hint μ) fun v hv => ?_
      have := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨v, hv⟩)
      exact this
    · right
      refine ⟨c, ?_⟩
      have := habove (μ'.toLinearMap - c • μ.toLinearMap)
        (fun g v => by simp [hint μ, hint μ']) (fun v hv => by
          have := LinearMap.congr_fun hc (Submodule.Quotient.mk ⟨v, hv⟩)
          rw [LinearMap.sub_apply, LinearMap.smul_apply]
          exact sub_eq_zero.2 this)
      exact sub_eq_zero.1 this

end GlobalTheory.FiltLevi

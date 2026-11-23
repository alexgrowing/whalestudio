import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} {K₀ : Type} {J₀ : K₀ → Type}

theorem eq_baseFull (k' : NonPluckerBlocks (blkF Ψ p q K₀)) {s : Ψ ⊕ Ψ} {a : Fin (rk Ψ p q s)}
    (hk : k'.1 = .inr ⟨s, a⟩) (h : 0 < rk Ψ p q s) : k' = baseFull K₀ s h := by
  have hfull : (a : ℕ) + 1 = rk Ψ p q s :=
    BasePt.step_full K₀ ⟨s, a⟩ (by rw [← hk]; exact k'.2)
  apply Subtype.ext
  rw [hk]
  have e : a = ⟨rk Ψ p q s - 1, by omega⟩ := Fin.ext (by show (a : ℕ) = rk Ψ p q s - 1; omega)
  rw [e]
  rfl

theorem xb_of_step [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)]
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (k' : NonPluckerBlocks (blkF Ψ p q K₀)) {s : Ψ ⊕ Ψ} {a : Fin (rk Ψ p q s)} (hk : k'.1 = .inr ⟨s, a⟩) :
    xb A x₀ ⟨k', c k'⟩ = zOf A c s := by
  have h : 0 < rk Ψ p q s := by have := a.2; omega
  obtain rfl := eq_baseFull k' hk h
  exact xb_rowsOf A x₀ c s h

theorem zOf_of_rk_eq_zero (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    {s : Ψ ⊕ Ψ} (h : rk Ψ p q s = 0) : zOf A c s = 1 := by
  haveI : IsEmpty (Fin (rk Ψ p q s)) := by rw [h]; infer_instance
  exact Matrix.det_isEmpty

open Classical in

def stepFac (z : Ω) (s : Ψ ⊕ Ψ) : K₀ ⊕ StepIx Ψ p q → Ω :=
  Sum.elim (fun _ => 1) fun t => if t.1 = s then z else 1

theorem prod_stepFac [Fintype Ψ] [Fintype K₀] (z : Ω) (s : Ψ ⊕ Ψ) (hz : rk Ψ p q s = 0 → z = 1) :
    ∏ k' : NonPluckerBlocks (blkF Ψ p q K₀), stepFac z s k'.1 = z := by
  classical
  by_cases h : 0 < rk Ψ p q s
  · rw [Finset.prod_eq_single (baseFull K₀ s h)]
    · simp [stepFac, baseFull, fullT]
    · rintro ⟨k | ⟨s', a⟩, hk⟩ _ hb
      · simp [stepFac]
      · by_cases e : s' = s
        · subst e
          exact absurd (eq_baseFull _ rfl h) hb
        · simp [stepFac, e]
    · simp
  · rw [hz (by omega)]
    refine Finset.prod_eq_one ?_
    rintro ⟨k | ⟨s', a⟩, hk⟩ _
    · simp [stepFac]
    · by_cases e : s' = s
      · subst e
        have := a.2
        omega
      · simp [stepFac, e]

theorem prod_xb_zpow_bF {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type}
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (r : Ψ × Fin (p + q)) :
    ∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      xcOf x₀ c ^ (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)) *
        (if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1) *
        (if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1) := by
  classical
  set N := rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1) with hN
  set zW : Ω := if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1 with hzW
  set zO : Ω := if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1 with hzO
  have hW : rk Ψ p q (.inl r.1) = 0 → zW = 1 := fun h => by
    rw [hzW, zOf_of_rk_eq_zero A c h]
    simp
  have hO : rk Ψ p q (.inr r.1) = 0 → zO = 1 := fun h => by
    rw [hzO, zOf_of_rk_eq_zero A c h]
    simp
  let g : NonPluckerBlocks (blkF Ψ p q K₀) → Ω := fun k' =>
    Sum.elim (fun _ => xb A x₀ ⟨k', c k'⟩ ^ N) (fun _ => 1) k'.1
  have hg : ∏ k', g k' = xcOf x₀ c ^ N := by
    rw [xcOf, ← Finset.prod_pow]
    refine (Fintype.prod_of_injective (baseInl (Ψ := Ψ) (p := p) (q := q)) ?_ _ _ ?_ ?_).symm
    · intro a b e
      exact Sum.inl.inj (congrArg Subtype.val e)
    · rintro ⟨k | t, hk⟩ hi
      · exact absurd ⟨k, rfl⟩ hi
      · rfl
    · intro k
      rfl
  have hpt : ∀ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      g k' * stepFac zW (.inl r.1) k'.1 * stepFac zO (.inr r.1) k'.1 := by
    rintro ⟨k | ⟨s, a⟩, hk⟩
    · have e : bF m r (⟨.inl k, hk⟩ : NonPluckerBlocks (blkF Ψ p q K₀)) = (N : ℤ) := rfl
      rw [e, zpow_natCast]
      simp [g, stepFac]
    · have hx := xb_of_step A x₀ c ⟨.inr ⟨s, a⟩, hk⟩ (s := s) (a := a) rfl
      have hf : (a : ℕ) + 1 = rk Ψ p q s := BasePt.step_full K₀ ⟨s, a⟩ hk
      rw [hx]
      rcases s with τ | τ
      · by_cases e : τ = r.1
        · subst e
          have hf' : (a : ℕ) + 1 = p := hf
          by_cases hc : p ≤ (r.2 : ℕ) + 1
          · simp [bF, twist, g, stepFac, hf', hc, hzW]
          · simp [bF, twist, g, stepFac, hf', hc, hzW]
        · simp [bF, twist, g, stepFac, e]
      · by_cases e : τ = r.1
        · subst e
          have hf' : (a : ℕ) + 1 = q := hf
          by_cases hc : (r.2 : ℕ) + 1 = p + q
          · simp [bF, twist, g, stepFac, hf', hc, hzO]
          · simp [bF, twist, g, stepFac, hf', hc, hzO]
        · simp [bF, twist, g, stepFac, e]
  rw [Finset.prod_congr rfl fun k' _ => hpt k', Finset.prod_mul_distrib, Finset.prod_mul_distrib, hg,
    prod_stepFac zW _ hW, prod_stepFac zO _ hO]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

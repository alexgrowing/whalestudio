import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder

noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.HeckeUOps

variable {D : D7}

theorem phase_ne_zero (τ : D.what₂.Tau) (a : D.host.Eˣ) :
    embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ) ≠ 0 := by
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  exact div_ne_zero h (by exact_mod_cast (norm_ne_zero_iff.2 h))

def mul {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (h : Even ((N₁ : ℤ) + N₂ - N)) : HeckeU D N where
  f := χ₁.f * χ₂.f
  n := χ₁.n + χ₂.n
  unitary x := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, χ₁.unitary, χ₂.unitary, one_mul]
  cont := by
    obtain ⟨m₁, hm₁, h₁⟩ := χ₁.cont
    obtain ⟨m₂, hm₂, h₂⟩ := χ₂.cont
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun u hu ⟨s, hs, e⟩ => ?_⟩
    rw [MonoidHom.mul_apply, h₁ u hu ⟨m₂ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; push_cast; ring⟩,
      h₂ u hu ⟨m₁ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; push_cast; ring⟩, one_mul]
  aut a := by
    have h1 := χ₁.aut a
    have h2 := χ₂.aut a
    have e : ∀ τ ∈ Finset.univ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ ((χ₁.n + χ₂.n) τ) =
        (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ) *
          (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ) := fun τ _ => by
      rw [Pi.add_apply, zpow_add₀ (phase_ne_zero τ a)]
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, MonoidHom.mul_apply, Units.val_mul]
    calc _ = (((χ₁.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ)) *
        (((χ₂.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  norm x := by rw [MonoidHom.mul_apply, χ₁.norm, χ₂.norm, one_mul]
  par τ := by
    have := (χ₁.par τ).add ((χ₂.par τ).add h)
    have e : (χ₁.n + χ₂.n) τ - (N : ℤ) = χ₁.n τ - N₁ + (χ₂.n τ - N₂ + (N₁ + N₂ - N)) := by
      simp only [Pi.add_apply]; ring
    rw [e]; exact this
  unr u hu hz := by rw [MonoidHom.mul_apply, χ₁.unr u hu hz, χ₂.unr u hu hz, one_mul]

def inv {N : ℕ} (N' : ℕ) (χ : HeckeU D N) (h : Even ((N : ℤ) - N')) : HeckeU D N' where
  f := χ.f⁻¹
  n := -χ.n
  unitary x := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, χ.unitary, inv_one]
  cont := by
    obtain ⟨m, hm, h₁⟩ := χ.cont
    exact ⟨m, hm, fun u hu hs => by rw [MonoidHom.inv_apply, h₁ u hu hs, inv_one]⟩
  aut a := by
    have h1 := χ.aut a
    have e : ∀ τ ∈ Finset.univ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ ((-χ.n) τ) =
        ((embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ.n τ))⁻¹ := fun τ _ => by
      rw [Pi.neg_apply, zpow_neg]
    rw [Finset.prod_congr rfl e, Finset.prod_inv_distrib, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, ← mul_inv, h1,
      inv_one]
  norm x := by rw [MonoidHom.inv_apply, χ.norm, inv_one]
  par τ := by
    have := ((χ.par τ).neg.sub h).sub (even_two_mul (N' : ℤ))
    have e : (-χ.n) τ - (N' : ℤ) = -(χ.n τ - N) - (N - N') - 2 * N' := by
      simp only [Pi.neg_apply]; ring
    rw [e]; exact this
  unr u hu hz := by rw [MonoidHom.inv_apply, χ.unr u hu hz, inv_one]

def ofChar (N : ℕ) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (hu : χ.IsUnitary) (hi : χ.HasInf (embT D) n)
    (hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1)
    (hn : ∀ x, χ.1 (finIdl D (x * sgU D x)) = 1) (hp : ∀ τ, Even (n τ - (N : ℤ)))
    (hr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1) :
    HeckeU D N where
  f := χ.1.comp (finIdl D)
  n := n
  unitary _ := hu _
  cont := hc
  aut a := by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ (hi a).symm
  norm := hn
  par := hp
  unr := hr

@[simp] theorem mul_f {N₁ N₂ N : ℕ} (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (h) (x) :
    (mul N χ₁ χ₂ h).f x = χ₁.f x * χ₂.f x := rfl

@[simp] theorem inv_f {N N' : ℕ} (χ : HeckeU D N) (h) (x) : (inv N' χ h).f x = (χ.f x)⁻¹ := rfl

@[simp] theorem ofChar_f (N : ℕ) (χ : HChar D.host.E) (n) (hu hi hc hn hp hr) (x) :
    (ofChar N χ n hu hi hc hn hp hr).f x = χ.1 (finIdl D x) := rfl

end GlobalTheory.HeckeUOps

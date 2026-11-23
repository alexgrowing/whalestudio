import Formalism.LocalToGlobal.ProjectiveLattices.FnDefB

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt_iff (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    rw [hval, ← hσ0]
    exact congrArg σ (Subtype.ext hx)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
        rw [← map_neg]
        exact congrArg σ (Subtype.ext hx)
      rw [← hval, h, hσ0] at h1
      exact h0 (by linear_combination h1 / 2)
    · exfalso
      exact h0 (by linear_combination (h.symm.trans hx) / 2)

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun z => Complex.conj_conj (τ z)

variable {σ : c.F →+* ℂ}

open Classical in

def letCol (U : Unf Xo c σ r) (k : U.Comp)
    (hmP : ∀ τ', relab c σ τ' ∈ (U.X k).Ψ → Dw.mult τ' + (U.X k).p0 ≤ r)
    (hmQ : ∀ τ', relab c σ τ' ∉ (U.X k).Ψ → conjEmb (relab c σ τ') ∈ (U.X k).Ψ ∧ Dw.mult τ' ≤ (U.X k).p0)
    (b : Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) : (U.X k).Ψ × Fin r :=
  if h : relab c σ b.1 ∈ (U.X k).Ψ then
    (⟨_, h⟩, ⟨(U.X k).p0 + b.2, by have := hmP _ h; have := b.2.isLt; omega⟩)
  else (⟨_, (hmQ _ h).1⟩, ⟨(U.X k).p0 - 1 - b.2, by have := (hmQ _ h).2; have := b.2.isLt; have := (U.X k).p0_le; omega⟩)

open Classical in

def aCol (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (k : U.Comp) (τ : (U.X k).Ψ) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) : ℝ)
  else -(a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℝ)

def nCol (U : Unf Xo c σ r) (n : ℕ) (k : U.Comp) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℝ) else -((n / 2 : ℕ) : ℝ)

end Formalism.L2.Pj

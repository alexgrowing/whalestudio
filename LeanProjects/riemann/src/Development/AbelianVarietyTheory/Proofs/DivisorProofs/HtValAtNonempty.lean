import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.Fin

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem htValAt_nonempty (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io)
    (hy : y₀.IsAlg) : (htValAt la y₀).Nonempty := by
  obtain ⟨p, hp, ha, k, y, h⟩ := (GlobalTheory.CompHt.exists_isHTFrameCp_and_nonempty E H Dw l Xo c).1 T io y₀ hy
  exact ⟨_, p, hp, ha, k, y, h, rfl⟩

theorem finConst_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (h₁ : HTConst U x) (h₂ : HTShift Xo c) :
    FinConst U x := fun Z τ s la => by
  obtain ⟨ρ, hρ⟩ := h₁ Z τ s la
  obtain ⟨κ, hκ⟩ := h₂ τ la
  refine ⟨ρ - κ, ?_⟩
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := htValAt_nonempty la y hy.1
  have h3 := (hρ w ⟨T, io, e, y, ho, hy, hw⟩).symm.trans (hκ T io e y ho hy.1 w hw _ s.sig_mem)
  show nval T.V e (evI y s.sig) = _
  by_cases h0 : evI y s.sig = 0
  · rw [h0, nval_zero, EReal.top_add_coe] at h3
    exact absurd h3 (EReal.coe_ne_top ρ)
  · rw [nval_of_ne h0] at h3 ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h3
    rw [EReal.coe_eq_coe_iff, h3]; ring

theorem finConst_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    Laws U x → HTShift Xo c → HTConst U x → FinConst U x :=
  by
  intro E _ _ _ H Dw l Xo c r U x _ h₂ h₁
  exact finConst_of h₁ h₂

end GlobalTheory.FlatCore.Fin

end

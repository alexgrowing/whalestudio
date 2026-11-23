import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LevelIdeal

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree

def levIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) : Ideal (𝓞 E) :=
  l.Mb ⊓ Ideal.span {(l.A : 𝓞 E)}

def levOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) {r : ℕ} (X : Data E r) :
    Subgroup (GL (Fin r) E) :=
  levelGrp (ccH E) X.Gm X.Λ (levIdeal l)

def UnfLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, SDTrace (U.X k).ξ0 (U.X k).Gm (U.X k).Λ

def UnfSign : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 0 < r → ∀ k, ∀ τ ∈ (U.X k).Ψ, (τ (U.X k).ξ0).im < 0

def UnfLevelIn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, ∀ γ ∈ levOf l (U.X k), ∀ x ∈ (U.X k).dom,
      ∃ γ' ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b

def UnfBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
      ∃ δ ∈ levOf l (U.X k), ∃ b : Frame (U.X k).Ψ r, lact γ x = rmul (lact δ x) b ∧
        ∀ τ (a a' : Fin r), (a' : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (a : ℕ) → b τ a a' = 0

def ScalarOfBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₀ : Subgroup (GL (Fin r) E))
    (γ : GL (Fin r) E), 0 < X.p0 → X.p0 < r →
    (∀ x ∈ X.dom, ∃ δ ∈ Γ₀, ∃ b : Frame X.Ψ r, lact γ x = rmul (lact δ x) b ∧
      ∀ τ (a a' : Fin r), (a' : ℕ) < X.p0 → X.p0 ≤ (a : ℕ) → b τ a a' = 0) →
    ∃ s : Eˣ, ∃ δ ∈ Γ₀, (δ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)

def OrbitsOfIncl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₀ : Subgroup (GL (Fin r) E)),
    (∀ γ ∈ X.Γ, ∃ s : Eˣ, ∃ δ ∈ Γ₀, (δ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)) →
    (∀ γ ∈ Γ₀, ∀ x ∈ X.dom, ∃ γ' ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ x = rmul (lact γ' x) b) →
    SameOrbits X X.Γ Γ₀

def EqVolUnf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 3 ≤ r → 0 < Dw.p → 0 < Dw.q →
    ∀ (k k' : U.Comp) (x : Frame (U.X k).Ψ r) (x' : Frame (U.X k').Ψ r) (FF : Set (V (nd (U.X k))))
      (FF' : Set (V (nd (U.X k')))), IsOrth (U.X k) x → IsOrth (U.X k') x' → IsFundSet (U.X k) x FF →
      IsFundSet (U.X k') x' FF' → muF (U.X k) x FF = muF (U.X k') x' FF'

theorem inf_span_ne_bot {R : Type} [CommRing R] [IsDomain R] {I J : Ideal R} {m a : R} (h : I * J = Ideal.span {m})
    (hm : m ≠ 0) (ha : a ≠ 0) : I ⊓ Ideal.span {a} ≠ ⊥ := by
  have h1 : m ∈ I * J := h ▸ Ideal.mem_span_singleton_self m
  have h2 : m * a ∈ I ⊓ Ideal.span {a} :=
    ⟨I.mul_mem_right _ (Ideal.mul_le_inf h1).1, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩
  intro h0
  rw [h0] at h2
  exact mul_ne_zero hm ha h2

theorem eqVolUnf_of (h0 : EqVolTr) (h1 : UnfLat) (h2 : UnfSign) (h3 : UnfLevelIn) (h4 : UnfBlock) (h5 : ScalarOfBlock)
    (h6 : OrbitsOfIncl)
    (h7 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H),
      Neat (IsCMField.complexConj E) l.Mb) : EqVolUnf := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr hp hq k k'
  have := H.unram
  have hp0 : ∀ k, (U.X k).p0 = Dw.q := fun k => (hU.2.1 k).1
  have hrk : r = Dw.p + Dw.q := hU.1
  have hpos : ∀ k, 0 < (U.X k).p0 := fun k => by rw [hp0]; exact hq
  have hlt : ∀ k, (U.X k).p0 < r := fun k => by rw [hp0]; omega
  have hO : ∀ k, SameOrbits (U.X k) (U.X k).Γ (levOf l (U.X k)) := fun k =>
    h6 E r _ _ (fun γ hγ => h5 E r _ _ γ (hpos k) (hlt k) (h4 E H Dw l Xo c σ r U hσ hU k γ hγ))
      (h3 E H Dw l Xo c σ r U hσ hU k)
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm
  have hne : levIdeal l ≠ ⊥ :=
    inf_span_ne_bot l.prod (Nat.cast_ne_zero.2 (by have := l.three_le; omega)) (Nat.cast_ne_zero.2 l.A_pos.ne')
  exact h0 E r (U.X k) (U.X k') _ _ (levIdeal l) _ _ hΨ ((hp0 k).trans (hp0 k').symm) hr (hpos k) (hlt k)
    ⟨(U.X k).Λ_fg, (U.X k).Λ_span⟩ ⟨(U.X k').Λ_fg, (U.X k').Λ_span⟩ (U.X k).ξ0_im (U.X k').ξ0_im
    (fun τ hτ => mul_pos_of_neg_of_neg (h2 E H Dw l Xo c σ r U hσ hU (by omega) k τ hτ)
      (h2 E H Dw l Xo c σ r U hσ hU (by omega) k' τ (hΨ ▸ hτ)))
    (h1 E H Dw l Xo c σ r U hσ hU k) (h1 E H Dw l Xo c σ r U hσ hU k') hne
    (neat_mono inf_le_left (h7 E H l)) (hO k) (hO k')

end PositivityTheory.EqVol

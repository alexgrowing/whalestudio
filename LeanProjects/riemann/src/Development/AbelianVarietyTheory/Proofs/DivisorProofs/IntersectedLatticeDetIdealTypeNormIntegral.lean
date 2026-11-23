import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LatticeIndex

theorem intersected_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.LevOK N M → ℓ.Prime → ∀ (A : GlobalTheory.PlaceInt.Adapt Λ N ℓ) (s : c.F), Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → ∀ e : ℕ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) := by
  intro E _ _ _ H Dw l c n Λ N M ℓ hL hl A s hs T io hu e
  have hN : N ≠ 0 := by rintro rfl; exact absurd hL.1 (by decide)
  let w := (valV (K' := T.Fr) T.V).comap io
  have hwi : ∀ x : c.F, IsIntegral ℤ x → w x ≤ 1 := fun x hx => valV_integral T
    (by convert map_isIntegral_int io hx; exact Subsingleton.elim _ _)
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => hwi _ r.isIntegral_coe
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hwi _ (map_isIntegral_int (embF c τ) r.isIntegral_coe)
  have hnat : ∀ τ (k : ℕ), Nat.Coprime k ℓ → w.comap (embF c τ) (k : E) = 1 := fun τ k hk => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valV_nat T hk hu
  have hn : ∀ τ, HasMax w (idealAt c Λ.Ln τ) (w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det)) := fun τ => by
    obtain ⟨a, b⟩ := detSet_Ln A _ (hwτ τ) (hnat τ _ A.cop₁)
    refine hasMax_span hw ?_ ⟨_, ⟨_, b, rfl⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have ha : ∀ τ, HasMax w (idealAt c Λ.La τ) (w.comap (embF c τ) A.ga.det)⁻¹ := fun τ => by
    obtain ⟨-, a, y, hy, b⟩ := detSet_La A _ (hwτ τ) (hnat τ _ A.cop)
    refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
    rintro _ ⟨y, hy, rfl⟩
    exact a y hy
  have h0 : ∀ τ, w.comap (embF c τ) A.ga.det ≠ 0 := fun τ => (detSet_La A _ (hwτ τ) (hnat τ _ A.cop)).1
  have hp : ∀ τ, w (embK c τ A.p.det) * (w.comap (embF c τ) A.ga.det)⁻¹ =
      w.comap (embF c τ) (algebraMap (𝓞 E) E A.g.det) := fun τ => by
    have := congrArg (w.comap (embF c τ)) (det_p A hN)
    simp only [map_mul, map_pow, hnat τ _ A.cop, hnat τ _ A.cop₁, _root_.one_pow, _root_.mul_one, _root_.one_mul] at this
    rw [mul_inv_eq_iff_eq_mul₀ (h0 τ), mul_comm]
    exact this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {s}) (w s) := hasMax_span hw (by simp) (by simp)
  have e1 := hb.mul (hasMax_prod hw Finset.univ _ _ fun τ => (hn τ).pow hw (Dw.mult τ))
  have e2 := hasMax_prod hw Finset.univ _ _ fun τ => (ha τ).pow hw (Dw.mult τ)
  obtain ⟨y, hy, hyv⟩ := e1.2
  have hle := e2.1 y (hs hy)
  rw [hyv] at hle
  simp only [← hp, mul_pow, Finset.prod_mul_distrib, ← _root_.mul_assoc] at hle
  have hpos : 0 < ∏ τ : E →+* ℂ, (w.comap (embF c τ) A.ga.det)⁻¹ ^ Dw.mult τ :=
    zero_lt_iff.2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (inv_ne_zero (h0 τ)))
  have hw1 : w (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≤ 1 := by
    rw [map_mul, map_prod]
    simp only [map_pow]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [_root_.one_mul]
    exact hle
  have hv : valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) ≤ 1 := hw1
  by_cases hx : io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) = 0
  · rw [hx, nval_zero]; exact le_top
  rw [nval_of_ne hx]
  have hlog : WithZero.log (valV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log (valV_ne_zero hx) one_ne_zero).2 hv
  have h0v : (0 : ℝ) ≤ (vV T.V (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) : ℝ) := by
    simp only [vV]; exact_mod_cast (by omega)
  exact EReal.coe_nonneg.2 (div_nonneg h0v (Nat.cast_nonneg _))

end GlobalTheory.LatticeIndex

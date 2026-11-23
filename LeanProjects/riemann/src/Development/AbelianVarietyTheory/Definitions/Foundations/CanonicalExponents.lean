import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

noncomputable section

namespace GlobalTheory.AllWt.Model

open NumberField IsDedekindDomain MeasureTheory Module

section Gram

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [StarRing K]

theorem deg_span {ι : Type} [Fintype ι] [DecidableEq ι] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) {j : ℕ} (hj : 0 < j) (e : Fin j → V) (he : LinearIndependent K e) :
    deg N (Submodule.span (𝓞 K) (Set.range e)) =
      -(1 / (2 * (Formalism.HN.nPl K : ℝ))) * Real.log (∏ v, (Formalism.HN.gramPl b X v e).det.re) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (h v).1
  have hL : (Submodule.span (𝓞 K) (Set.range e)).FG := Submodule.fg_span (Set.finite_range e)
  have hne : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥ := fun h0 => by
    have : e ⟨0, hj⟩ ∈ Submodule.span (𝓞 K) (Set.range e) := Submodule.subset_span ⟨_, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact he.ne_zero _ this
  have hrk : Formalism.HN.rkK (Submodule.span (𝓞 K) (Set.range e)) = j := by
    rw [Formalism.HN.rkK, Submodule.span_span_of_tower, finrank_span_eq_card he, Fintype.card_fin]
  have h1 := (Formalism.HN.sizeMu K V ι b X hX _ hL hne).2.1
  have h2 := (Formalism.HN.htGram K V ι b X hX j e he).1
  have h3 := (Formalism.HN.plLat K V ι b X hX _ hL).2.2
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl; exact_mod_cast Fintype.card_pos
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  rw [deg, slope, slope_sq_eq h hL, h1, Formalism.HN.size, Real.log_rpow h3, h2, hrk]
  field_simp

omit [StarRing K] in

theorem deg_two : deg (fun (σ : K →+* ℂ) (y : K) => ‖σ y‖) (Submodule.span (𝓞 K) {(2 : K)}) = -Real.log 2 := by
  have hrk : Formalism.HN.rkK (Submodule.span (𝓞 K) {(2 : K)}) = 1 := by
    rw [Formalism.HN.rkK, Submodule.span_span_of_tower, finrank_span_singleton two_ne_zero]
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl; exact_mod_cast Fintype.card_pos
  have hv : ∀ v : InfinitePlace K, v 2 = 2 := fun v => by
    rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; simp
  rw [deg, slope, slope_sq_line 2 two_ne_zero, hrk]
  simp only [hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (Fintype.card (InfinitePlace K) : ℝ) = Formalism.HN.nPl K from rfl]
  field_simp
  simp

end Gram

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem bar_gap (a : (E →+* ℂ) × ℕ → ℤ) (m : ℤ) (τ : Psi H) (hp : 0 < Dw.p) (hq : 0 < Dw.q) :
    weightOf Dw a m τ ⟨Dw.p - 1, by omega⟩ - weightOf Dw a m τ ⟨Dw.p, by omega⟩ =
      a (τ.1, Dw.p - 1) + a (conjEmb τ.1, Dw.q - 1) + 2 * m := by
  have h1 : Dw.p - 1 < Dw.p := by omega
  simp only [weightOf, h1, if_true, lt_irrefl, if_false, Nat.sub_self, Nat.sub_zero]
  ring

theorem small_antitone (la : Weight Dw) (m : ℤ) (τ : Psi H)
    (h : ∀ i j : Fin (Dw.p + Dw.q), Dw.p ≤ i → i ≤ j → la τ j ≤ la τ i) (i j : ℕ) (hij : i ≤ j) (hj : j < Dw.q) :
    (wtOf Dw la m).1 (conjEmb τ.1, j) ≤ (wtOf Dw la m).1 (conjEmb τ.1, i) := by
  rw [wtOf_small la m τ j hj, wtOf_small la m τ i (by omega)]
  have := h ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (by simp)
    (by simp only [Fin.mk_le_mk]; omega)
  omega

theorem canonical_exponents (τ : Psi H) (i j : ℕ) (hi : i < Dw.p) (hj : j < Dw.q) :
    (wtOf Dw (fun _ k => if (k : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)) 0).1 (τ.1, i) = Dw.q ∧
      (wtOf Dw (fun _ k => if (k : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)) 0).1 (conjEmb τ.1, j) = Dw.p := by
  rw [wtOf_big _ _ _ _ hi, wtOf_small _ _ _ _ hj]; simp [hi]

variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem modelWt_eq_sub {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (G : WTZ E) (hG : Even G.2) :
    ∃ a n a' n', Dom a n ∧ Dom a' n' ∧ ∀ k, laU U a' n' k = modelWt U G k + laU U a n k := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ (τ : E →+* ℂ) (i : Fin r), (G.1 (τ, i)).natAbs ≤ B :=
    ⟨Finset.univ.sup fun x : (E →+* ℂ) × Fin r => (G.1 (x.1, x.2)).natAbs, fun τ i =>
      Finset.le_sup (f := fun x : (E →+* ℂ) × Fin r => (G.1 (x.1, x.2)).natAbs) (Finset.mem_univ (τ, i))⟩
  have hB' : ∀ τ i, i < r → -(B : ℤ) ≤ G.1 (τ, i) ∧ G.1 (τ, i) ≤ B := fun τ i hi => by
    have := hB τ ⟨i, hi⟩
    simp only at this
    omega
  obtain ⟨s, hs⟩ := hG
  have hpos : ∀ τ i, i < r → 0 ≤ G.1 (τ, i) + ((2 * B * (r - i) : ℕ) : ℤ) := fun τ i hi => by
    have h1 := (hB' τ i hi).1
    have h2 : 2 * B * 1 ≤ 2 * B * (r - i) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨fun x => 2 * B * (r - x.2), 2 * s.natAbs,
    fun x => if x.2 < r then (G.1 x + ((2 * B * (r - x.2) : ℕ) : ℤ)).toNat else 0, 2 * (s + s.natAbs).toNat,
    ⟨fun τ i j hij => Nat.mul_le_mul_left _ (by omega), even_two_mul _⟩,
    ⟨fun τ i j hij => ?_, even_two_mul _⟩, fun k => ?_⟩
  · simp only
    split_ifs with h1 h2 h2
    · rcases hij.eq_or_lt with rfl | hlt
      · exact le_rfl
      · have e1 := hB' τ i h2
        have e2 := hB' τ j h1
        have e3 : 2 * B * (r - j) + 2 * B * 1 ≤ 2 * B * (r - i) := by
          rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
        omega
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  · funext τ j
    have hj := j.2
    have hp := (U.X k).p0_le
    simp only [laU, modelWt, Pi.add_apply]
    split_ifs with h1 h2 h2
    · rw [Int.toNat_of_nonneg (hpos _ _ h2)]; omega
    · omega
    · rw [Int.toNat_of_nonneg (hpos _ _ h2)]; omega
    · omega

theorem chi_modelWt {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (h : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (G : WTZ E) (hG : Even G.2) (k : U.Comp) : ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1 := by
  intro γ hγ
  obtain ⟨a, n, a', n', h1, h2, h3⟩ := modelWt_eq_sub U G hG
  have := h a' n' h2 k γ hγ
  rwa [h3, (U.X k).χ_add _ _ γ hγ, h a n h1 k γ hγ, mul_one] at this

end GlobalTheory.AllWt.Model

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FractionalSliceDomains
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace SliceBounds

variable {r : ℕ} (X : Data E r)

theorem slice_bound {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (C A : ℝ)
    (hmod : ∀ z ∈ X.dom, X.pnorm la P z ≤ C * X.la1 z ^ (-A)) {n : ℕ}
    (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)) (hω : Submodule.span ℤ (Set.range ω) = RealEmbeddingCharacters.perL X la)
    {b : Fin n → ℝ} (hb : b ∈ Om X ξ x ω) {k1 k2 R : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2)
    (hq1 : ∀ τ (ρ : ℝ), |ρ| ≤ Bω X ω →
      k1 ≤ min (1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ))⁻¹ /
        (1 + X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2)
    (hq2 : ∀ τ (ρ : ℝ), |ρ| ≤ Bω X ω →
      max (1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
        (1 + X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤ k2)
    (hR : ∏ τ, max (1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ))⁻¹ ^ (X.spread la τ / 2) ≤ R)
    (y : Fin n → ℝ) :
    ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (b k : ℂ) * I)‖ * X.nfac la x ≤
      max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by
  classical
  rw [slice_fract (X := X) (ω := ω) P la hP hx hξ hω hb y]
  set u : Fin n → ℝ := fun k => Int.fract (y k) with hu
  set s : X.Ψ → ℂ := fun τ => ∑ j, (((u j : ℝ) : ℂ) + (b j : ℂ) * I) * (ω j τ : ℂ) with hs
  have hre : ∀ τ, (s τ).re = ∑ j, u j * ω j τ := by
    intro τ
    simp [hs, Complex.re_sum]
  have him : ∀ τ, (s τ).im = ∑ j, b j * ω j τ := by
    intro τ
    simp [hs, Complex.im_sum]
  have hhf : hfun X P ξ x ω (fun k => ((u k : ℝ) : ℂ) + (b k : ℂ) * I) = P (X.flow ξ s x) := by
    simp only [hfun, hs]
  have hsim : (fun τ => (s τ).im) = fun τ => ∑ j, b j * ω j τ := funext him
  have hdom : X.flow ξ s x ∈ X.dom := by
    rw [AdmissibleHermitianColumns.flow_mem_dom_iff (X := X) hξ.2.1 x hx, hsim]
    exact hb
  have hbd : ∀ τ, |(s τ).re| ≤ Bω X ω := by
    intro τ
    rw [hre]
    exact re_bound (X := X) (ω := ω) u (fun j => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩) τ
  rw [hhf]
  have hisoV : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := by
    intro τ
    constructor
    · have hh : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
        simp only [hermC, herm, Data.emb, map_sum, map_mul]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        congr 1
        exact (IsCMField.complexEmbedding_complexConj E τ.1 (ξ b)).symm
      rw [hh, hξ.2.1, map_zero]
    · intro h
      apply hξ.2.2
      funext a
      have ha := congrFun h a
      simpa [Data.emb] using ha
  have hflowV : X.flowV (fun τ => Data.emb τ.1 ξ) s x = X.flow ξ s x := rfl
  have hN := (m3bNorm_holds (E := E) r X (fun τ => Data.emb τ.1 ξ) hisoV la x hx s
    (by rw [hflowV]; exact hdom)).2
  rw [hflowV] at hN
  refine MinimumGrowthBounds.growth (X := X) la P C A hmod hx hdom hk1 hk12 ?_ ?_ ?_
  · intro τ w
    have h := (TwoSidedBoostBounds.maj_two_sided (X := X) hx hξ s hdom τ w).2.1
    rw [him τ] at h
    exact le_trans (mul_le_mul_of_nonneg_right (hq1 τ _ (hbd τ)) (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ w)) h
  · intro τ w
    have h := (TwoSidedBoostBounds.maj_two_sided (X := X) hx hξ s hdom τ w).2.2
    rw [him τ] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (hq2 τ _ (hbd τ)) (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ w))
  · refine le_trans hN (le_of_eq_of_le ?_ hR)
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    have hA : 1 + (s τ).im / X.ttV (fun τ => Data.emb τ.1 ξ) x τ =
        1 + X.c τ * (∑ j, b j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ) := by
      rw [him τ, Data.ttV, one_div, div_inv_eq_mul]
      ring
    beta_reduce
    rw [hA]

end SliceBounds

end ReciprocityTheory.ChartRestriction.G.FD

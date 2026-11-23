import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNormStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMulStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslationsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescripStatement
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem uu_eq_pull_reach : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → ∀ (s : SecN Xo x 1) (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (x₁ ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 → (x₂ ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → N ^ 2 = n' ^ 2 * A * Bn ∧ ∃ hh : SecN Xo x (n' ^ 2 * A), Reach Xo s (n' ^ 2 * A) hh ∧ Pulls Xo β hh (sqN Xo N F) := by
  intro E _ _ _ H Dw l Xo S _ x N n' A Bn α β hodd hN hα hβ s x₁ x₂ F h₁ h₂ h₁' h₂' hUU
  have hαβ : (α * β) * H.bar (α * β) = ((A * Bn : ℕ) : 𝓞 E) := by
    rw [map_mul, Nat.cast_mul, ← hα, ← hβ]; ring
  have hn : (n' : 𝓞 E) * H.bar (n' : 𝓞 E) = ((n' ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow]; ring
  have hNN : (N : 𝓞 E) * H.bar (N : 𝓞 E) = ((N ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow]; ring
  have hN' : (n' : 𝓞 E) * (α * β) = (N : 𝓞 E) := by rw [hN]; ring
  have hsq : N ^ 2 = n' ^ 2 * A * Bn := by
    have h : ((N ^ 2 : ℕ) : 𝓞 E) = ((n' ^ 2 * A * Bn : ℕ) : 𝓞 E) := by
      rw [← hNN, ← hN', map_mul, mul_assoc (n' ^ 2), Nat.cast_mul (n' ^ 2), ← hn, ← hαβ]; ring
    exact_mod_cast h
  have hoN : Odd (N ^ 2) := hodd.pow
  have ho3 : Odd (n' ^ 2 * A * Bn) := hsq ▸ hoN
  have ho2 : Odd (n' ^ 2 * A) := (Nat.odd_mul.1 ho3).1
  have ho1 : Odd (n' ^ 2) := (Nat.odd_mul.1 ho2).1
  have hoA : Odd A := (Nat.odd_mul.1 ho2).2
  have hlev : n' ^ 2 = 1 ∨ 4 ≤ n' ^ 2 := by
    rcases n' with _ | _ | m
    · simp at ho1
    · left; rfl
    · right; exact Nat.pow_le_pow_left (n := 2) (by omega) 2
  refine ⟨hsq, ?_⟩
  obtain ⟨F₀, F₁, hF₀, hF₁, hF₂⟩ := ((GlobalTheory.T.symmetricTranslates_multiplication_pullback_description E H Dw l Xo S x N hodd s).1 x₁ x₂ F h₁ h₂).1 hUU
  obtain ⟨G₀, hG₀, -⟩ := GlobalTheory.T.existsUnique_normalisedPullback_rational_norm E H Dw l Xo S x (n' : 𝓞 E) (n' ^ 2) 1 (n' ^ 2) hn (Nat.one_mul _).symm s
  obtain ⟨G₁, hG₁, -⟩ := (GlobalTheory.T.existsUnique_symmetricTranslate_oddLevel E H Dw l Xo S x (n' ^ 2) ho1 _ h₁' G₀).1
  obtain ⟨K₁, hK₁, -⟩ := GlobalTheory.T.existsUnique_normalisedPullback_rational_norm E H Dw l Xo S x α A (n' ^ 2) (n' ^ 2 * A) hα rfl G₁
  obtain ⟨hh, hhh, -⟩ := (GlobalTheory.T.existsUnique_symmetricTranslate_oddLevel E H Dw l Xo S x (n' ^ 2 * A) ho2 _ h₂' K₁).1
  refine ⟨hh, ?_, ?_⟩
  · refine Reach.move _ _ K₁ hh (Reach.pull (n' ^ 2) A _ α G₁ K₁ ?_ hlev hoA hα rfl hK₁) hhh
    refine Reach.move _ _ G₀ G₁ ?_ hG₁
    exact Reach.pull 1 (n' ^ 2) _ _ s G₀ Reach.base (Or.inl rfl) ho1 hn (Nat.one_mul _).symm hG₀
  · have hsq' : N ^ 2 = n' ^ 2 * (A * Bn) := by rw [hsq, Nat.mul_assoc]
    obtain ⟨P, hP, -⟩ := GlobalTheory.T.existsUnique_normalisedPullback_rational_norm E H Dw l Xo S x (α * β) (A * Bn) (n' ^ 2) (N ^ 2) hαβ hsq' G₀
    obtain ⟨Q, hQ, -⟩ := GlobalTheory.T.existsUnique_normalisedPullback_rational_norm E H Dw l Xo S x β Bn (n' ^ 2 * A) (N ^ 2) hβ hsq K₁
    obtain ⟨R, hR, -⟩ := GlobalTheory.T.existsUnique_normalisedPullback_rational_norm E H Dw l Xo S x β Bn (n' ^ 2 * A) (N ^ 2) hβ hsq hh
    have hPN : Pulls Xo (N : 𝓞 E) s P := hN' ▸ GlobalTheory.T.isNormalisedPullbackSection_mul E H Dw l Xo S x _ _ _ _ _ s G₀ P hG₀ hP
    have hPF : P = F₀ :=
      (GlobalTheory.T.existsUnique_normalisedPullback_rational_norm E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) hNN (Nat.one_mul _).symm s).unique hPN hF₀
    have hQ' : Pulls Xo (α * β) G₁ Q := GlobalTheory.T.isNormalisedPullbackSection_mul E H Dw l Xo S x _ _ _ _ _ G₁ K₁ Q hK₁ hQ
    have hm₁ : Moves Xo x₁ P Q :=
      GlobalTheory.T.normalisedPullback_commutes_symmetric_translations E H Dw l Xo S x (α * β) (A * Bn) _ _ hαβ hsq' hoN _ x₁ rfl h₁ G₀ G₁ P Q hG₁ hP hQ'
    have hQF : Q = F₁ := (GlobalTheory.T.existsUnique_symmetricTranslate_oddLevel E H Dw l Xo S x (N ^ 2) hoN x₁ h₁ F₀).1.unique (hPF ▸ hm₁) hF₁
    have hm₂ : Moves Xo x₂ Q R :=
      GlobalTheory.T.normalisedPullback_commutes_symmetric_translations E H Dw l Xo S x β Bn _ _ hβ hsq hoN _ x₂ rfl h₂ K₁ hh Q R hhh hQ hR
    have hRF : R = sqN Xo N F := (GlobalTheory.T.existsUnique_symmetricTranslate_oddLevel E H Dw l Xo S x (N ^ 2) hoN x₂ h₂ F₁).1.unique (hQF ▸ hm₂) hF₂
    exact hRF ▸ hR

end GlobalTheory.PlaceInt

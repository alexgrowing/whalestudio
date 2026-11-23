import Formalism.LocalToGlobal.UnitaryNorms.CharExEta

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

open Classical in

structure EtaHostFacts {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) : Prop where

  unram : ∀ P : HeightOneSpectrum (𝓞 H.E), (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 H.F) = 1

  totReal : ∀ w : InfinitePlace H.F, w.IsReal

  onePsi : ∀ w : InfinitePlace H.F,
    (Finset.univ.filter (fun i => InfinitePlace.mk (embPsi H i) ∈ aboveInf (L := H.E) H.F w)).card = 1

  conj : ∃ c : H.E →ₐ[H.F] H.E, (∀ x, c (c x) = x) ∧ (∀ x, c x = x → ∃ a : H.F, algebraMap H.F H.E a = x) ∧
    (∀ (φ : H.E →+* ℂ) (x : H.E), φ (c x) = starRingEnd ℂ (φ x)) ∧ c H.sqrtMinusD = -H.sqrtMinusD

  roots : ∀ z : H.E, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → z = 1 ∨ z = -1
  sqrt_ne : H.sqrtMinusD ≠ 0

  sqrt_pos : ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → ∀ i, ∃ r : ℝ, 0 < r ∧ embPsi H i (s : H.E) = Complex.I * r

  card4 : 4 ∣ Fintype.card (R.Psi)

  dsplit : ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD →
    ∀ P : HeightOneSpectrum (𝓞 H.E), ordF P s ≠ 0 → (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card ≠ 1

end CharEx

end Formalism.L2.Host

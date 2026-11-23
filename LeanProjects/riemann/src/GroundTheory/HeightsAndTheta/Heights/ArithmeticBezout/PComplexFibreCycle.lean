import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ComplexFibreIdealBot
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealNeBotDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PSpecFirstMemIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.AevalGenericIdealIff
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace ComplexFibreCycle

theorem complexFibreIdeal_eq_map {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    complexFibreIdeal P = (ObjectsChow.genericIdeal P).map (MvPolynomial.map (Rat.castHom ℂ)) := by
  have h : (MvPolynomial.map (Rat.castHom ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) :=
    RingHom.ext fun p => by
      rw [RingHom.comp_apply, MvPolynomial.map_map,
        RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]
  rw [complexFibreIdeal, ObjectsChow.genericIdeal, Ideal.map_map, h]

theorem specFirst_eq_zero_iff (hNe : SpecFirstNe.Statement) (hBot : IncIdealNeBotDim.Statement)
    (hDim : ConeDimOfChowForm.Statement) {n e : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hW : IsProjPrime W) (hg : IsChowForm W (e + 1) g)
    (u : Fin n → ℂ) : IndefiniteRowSideFullHecke.ArithBezout.specFirst u g = 0 ↔ linForm u ∈ W := by
  rw [← ObjectsChow.specFirst_eq]
  constructor
  · intro h
    by_contra hu
    exact hNe ℂ n e W g u hW hg hu h
  · intro hu
    have hbot : incIdeal W e = ⊥ := by
      by_contra hne
      have h1 := hBot ℂ n e W hW hne
      rw [hDim ℂ n (e + 1) W g hW hg] at h1
      have h2 : ((e + 1 : ℕ) : ℕ∞) ≤ ((e : ℕ) : ℕ∞) := by exact_mod_cast h1
      have h3 : e + 1 ≤ e := by exact_mod_cast h2
      omega
    have h := SpecFirstMemIncIdeal.proof ℂ n e W W g u hg le_rfl hu
    rwa [hbot, Ideal.mem_bot] at h

end ComplexFibreCycle

open ComplexFibreCycle in

theorem ComplexFibreCycle.proof (hBC : ChowFormBaseChange.Statement) (hNe : SpecFirstNe.Statement)
    (hBot : IncIdealNeBotDim.Statement) (hDim : ConeDimOfChowForm.Statement) :
    ComplexFibreCycle.Statement := by
  intro n e δ P f hP hf
  obtain ⟨c, hc, f₀, rfl, hf₀⟩ := ObjectsChow.ComplexChowFormToChowForm.proof n e δ P f hP hf
  have hI := (ObjectsChow.GenericFibreIdeal.proof n (e + 1) P hP).1
  have key := hBC ℚ n (e + 1) (ObjectsChow.genericIdeal P) f₀ (Rat.castHom ℂ) hI hf₀
  rw [← complexFibreIdeal_eq_map] at key
  obtain ⟨hprime, c', hc', g, hg, hfeq⟩ := key
  have hCne : ∀ {k : ℕ} (a : ℂ), a ≠ 0 → (C a : MvPolynomial (Fin k × Fin n) ℂ) ≠ 0 :=
    fun a ha => by rwa [Ne, C_eq_zero]
  refine ⟨hprime, ?_, fun u => ?_⟩
  · unfold IsChowFormCycle
    exact ⟨c * c', mul_ne_zero hc hc', g, hg, by rw [hfeq, ← mul_assoc, ← C_mul]⟩
  · have hsC : ∀ a : ℂ, IndefiniteRowSideFullHecke.ArithBezout.specFirst (e := e) u (C a) = C a := by
      intro a
      simp [IndefiniteRowSideFullHecke.ArithBezout.specFirst]
    rw [hfeq, map_mul, map_mul, hsC, hsC, map_prod]
    simp only [map_pow]
    constructor
    · intro h W hW hu
      apply h
      rw [Finset.prod_eq_zero hW, mul_zero, mul_zero]
      rw [(specFirst_eq_zero_iff hNe hBot hDim (hprime W hW) (hg W hW) u).mpr hu,
        zero_pow (Finsupp.mem_support_iff.mp hW)]
    · intro h
      refine mul_ne_zero (hCne c hc) (mul_ne_zero (hCne c' hc')
        (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ ?_))
      rw [Ne, specFirst_eq_zero_iff hNe hBot hDim (hprime W hW) (hg W hW) u]
      exact h W hW

end GroundTheory.Heights₂.Heights

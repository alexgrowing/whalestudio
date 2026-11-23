import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AutomorphicArithmetic.CMTraceForms.Places
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwoStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum

theorem extendedReal_coe_finset_sum_of_real {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem oscLe_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p hp vd hvd hT
  classical
  intro la
  refine ⟨0, fun T io e ho y => ?_⟩
  have hfall : ∀ f : Lt1 Dw, letI := H.starRing
      (((0 : ℝ) : EReal) ≤ nuFac p y f (cx f) ∧ (y.IsAlg → nuFac p y f (cx f) ≤ ((boundAll p (rk f) (cx f) : ℝ) : EReal))) :=
    fun f => ((GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y)
  have hnu : letI := H.starRing; nuP p y cx = ∑ f, nuFac p y f (cx f) := rfl
  refine ⟨?_, fun hy => ?_⟩
  · simp only [Nat.cast_zero, EReal.coe_zero] at hfall ⊢
    rw [hnu]
    exact Finset.sum_nonneg fun f _ => (hfall f).1
  · obtain ⟨len, hlen0, -, hlenS, hlen⟩ :=
      GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo E H Dw l Xo c p F vd hT T io y (not_isUnit_of_overLa la ho) hy
    set b : Lt1 Dw → ℝ := fun f => if IsBig k f then (cx f : ℝ) * len f.1 else (rk f : ℝ) * cx f with hb
    have hfb : ∀ f, letI := H.starRing; nuFac p y f (cx f) ≤ ((b f : ℝ) : EReal) := by
      intro f
      by_cases hbig : IsBig k f
      · simp only [hb, if_pos hbig]
        simpa [mul_comm] using hlen f (cx f) hbig.1
      · simp only [hb, if_neg hbig]
        have := (hfall f).2 hy
        have hB : boundAll p (rk f) (cx f) ≤ (rk f : ℝ) * cx f := by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
          unfold boundAll
          exact div_le_self (by positivity) (by linarith)
        exact this.trans (EReal.coe_le_coe_iff.2 hB)
    have hsum : letI := H.starRing; nuP p y cx ≤ ((∑ f, b f : ℝ) : EReal) := by
      rw [hnu, extendedReal_coe_finset_sum_of_real]
      exact Finset.sum_le_sum fun f _ => hfb f
    refine hsum.trans (EReal.coe_le_coe_iff.2 ?_)
    have hsplit : ∑ f, b f = (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) +
        ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f := by
      simp only [hb]; rw [Finset.sum_ite]
    have hsmall : (∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * cx f) ≤ Sm := by
      refine le_trans (le_of_eq ?_) hE.2.2.1
      unfold sumSmallSpread
      push_cast
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext f; simp [not_isBig_iff]
    have hbig : (∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * len f.1) ≤ F * m * (1 + vd / 2) * Mb := by
      have hfib := Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)
        (fun f => (cx f : ℝ) * len f.1)
      rw [← hfib]
      have h1 : ∀ τ : E →+* ℂ, (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
          ≤ len τ * Mb := by
        intro τ
        have hτ := hE.2.1 τ
        have : (∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
            = len τ * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), (cx f : ℝ) := by
          rw [Finset.filter_filter, Finset.mul_sum]
          refine Finset.sum_congr (by ext f; simp) fun f hf => ?_
          rw [(Finset.mem_filter.1 hf).2.2, mul_comm]
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (hlen0 τ)
        rw [Nat.cast_sum] at hτ
        refine le_trans (le_of_eq ?_) hτ
        exact Finset.sum_congr (by ext f; simp) fun _ _ => rfl
      have hq : (Dw.q : ℝ) ≤ m := by exact_mod_cast hS.2.1
      calc _ ≤ ∑ τ : E →+* ℂ, len τ * Mb := Finset.sum_le_sum fun τ _ => h1 τ
        _ = (∑ τ, len τ) * Mb := by rw [Finset.sum_mul]
        _ ≤ (F * Dw.q * (1 + vd / 2)) * Mb := mul_le_mul_of_nonneg_right hlenS hE.1
        _ ≤ F * m * (1 + vd / 2) * Mb := by
          apply mul_le_mul_of_nonneg_right _ hE.1
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    simp only [Nat.cast_zero, zero_add]
    rw [hsplit]
    linarith

end GlobalTheory.RefSum

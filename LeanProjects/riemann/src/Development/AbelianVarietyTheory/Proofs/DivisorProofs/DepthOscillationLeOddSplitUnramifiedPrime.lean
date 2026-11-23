import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OscSplit

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumBig sumSmallSpread not_isBig_iff)

theorem ereal_coe_sum {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

theorem card_filter_inPsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← GlobalTheory.LamF.card_psiSet H, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)

open Classical in

theorem sumBig_le {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {F k : ℕ} {Mb : ℝ} {cx : Lt1 Dw → ℕ}
    (hF : Module.finrank ℚ E = 2 * F)
    (h : ∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) :
    (sumBig k cx : ℝ) ≤ F * Mb := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi, hF]; omega
  have e : sumBig k cx = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ),
      ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f := by
    unfold sumBig
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (IsBig k))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.filter_filter]
  rw [e, Nat.cast_sum]
  refine (Finset.sum_le_sum fun τ _ => h τ).trans ?_
  rw [Finset.sum_const, hc, nsmul_eq_mul]

theorem oscLe_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp h2 hd hs la
  classical
  obtain ⟨-, hqm, -, -, -, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hB
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  let B : Lt1 Dw → ℝ := fun f =>
    if IsBig k f then (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) else boundAll p (rk f) (cx f)
  have hsum : ∑ f, B f ≤ (F * m * Mb + Sm) / ((p : ℝ) - 1) := by
    have e1 : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) =
        (sumBig k cx : ℝ) * Dw.q / ((p : ℝ) - 1) := by
      rw [← Finset.sum_mul, mul_div_assoc, sumBig, Nat.cast_sum]
    have e2 : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) =
        (sumSmallSpread k cx : ℝ) / ((p : ℝ) - 1) := by
      rw [sumSmallSpread, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr (Finset.filter_congr fun f _ => not_isBig_iff k f) fun f _ => ?_
      rw [boundAll, Nat.cast_mul]
    have h1 := sumBig_le (k := k) (cx := cx) hF hbig
    have h3 : (Dw.q : ℝ) ≤ m := by exact_mod_cast hqm
    have h4 : (sumBig k cx : ℝ) * Dw.q ≤ F * Mb * m :=
      mul_le_mul h1 h3 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMb)
    rw [Finset.sum_ite, e1, e2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨0, fun T io e ho y => ?_⟩
  have hall := fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y
  constructor
  · rw [Nat.cast_zero, EReal.coe_zero]
    exact Finset.sum_nonneg fun f _ => (hall f).1
  · intro ha
    rw [Nat.cast_zero, zero_add]
    refine le_trans ?_ (EReal.coe_le_coe_iff.2 hsum)
    rw [ereal_coe_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : IsBig k f
    · simp only [B, if_pos hf]
      exact (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) ha h2 hd f (cx f) hf.1).1 hs
    · simp only [B, if_neg hf]
      exact (hall f).2 ha

end GlobalTheory.OscSplit

end

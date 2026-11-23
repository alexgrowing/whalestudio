import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
namespace GlobalTheory.RefSum

theorem nuBetween_sum_and_eLoc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  intro E _ _ _ H Dw l Xo c p _ la cx
  letI := H.starRing
  have hcs : ∀ g : Lt1 Dw → ℝ, (((∑ f, g f : ℝ)) : EReal) = ∑ f, ((g f : ℝ) : EReal) := fun g =>
    map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ
  refine ⟨fun A B hAB => ⟨fun T io e ho y => ⟨?_, fun ha => ?_⟩, ?_⟩, ?_⟩
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
  · set s : ℝ := ∑ f, A f with hs
    refine ⟨⌊max 0 s⌋₊, fun T io e ho y => ⟨?_, fun ha => ?_⟩⟩
    · have h0 : (0 : EReal) ≤ nuP p y cx := Finset.sum_nonneg fun f _ =>
        (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y |>.1 |> fun h => by simpa using h
      have h1 : ((s : ℝ) : EReal) ≤ nuP p y cx := by
        rw [hs, hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
      have hn : ((⌊max 0 s⌋₊ : ℕ) : ℝ) ≤ max 0 s := Nat.floor_le (le_max_left _ _)
      rcases le_total 0 s with h | h
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_right h).le)).trans h1
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_left h).le)).trans (by simpa using h0)
    · have hu : nuP p y cx ≤ ((∑ f, B f : ℝ) : EReal) := by
        rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
      refine hu.trans (EReal.coe_le_coe_iff.2 ?_)
      have hlt : max 0 s < ((⌊max 0 s⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsd : ∑ f, (B f - A f) = ∑ f, B f - s := by rw [Finset.sum_sub_distrib]
      have hm : s ≤ max 0 s := le_max_right _ _
      linarith
  · intro b hb O _ β Y Z
    obtain ⟨A, hA⟩ := hb la
    calc eLoc Y Z la cx ≤ ((((A : ℝ) + b : ℝ)) : EReal) - (((A : ℝ)) : EReal) :=
          EReal.sub_le_sub (nuPSup_le fun T io e ho y hy => (hA T io e ho y).2 hy.2)
            (le_nuPInf fun T io e ho y _ => (hA T io e ho y).1)
      _ = (b : EReal) := by rw [← EReal.coe_sub]; congr 1; ring

end GlobalTheory.RefSum

end

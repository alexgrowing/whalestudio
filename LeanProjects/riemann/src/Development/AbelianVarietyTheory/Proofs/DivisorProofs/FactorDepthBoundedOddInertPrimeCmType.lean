import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDepthLowerBoundSaturatedEvenTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrimeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem inPsi_orbit_parity {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {h : ℕ}
    (hh : 0 < h) (lab : ZMod h → (E →+* ℂ)) (hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s))
    (h0 : InPsi H (lab 0)) : Even h ∧ ∀ s : ZMod h, InPsi H (lab s) ↔ Even s.val := by
  have hn : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, Nat.even_add_one]
  haveI : NeZero h := ⟨hh.ne'⟩
  refine ⟨(hn h).1 (by simpa [ZMod.natCast_self] using h0), fun s => ?_⟩
  have := hn s.val
  rwa [ZMod.natCast_zmod_val] at this

theorem facBetween_fine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → 1 ≤ k → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundFine p (Dw.p + Dw.q) Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hp2 hdisc hin f k hf hk
  letI := H.starRing
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hL : 0 ≤ Real.logb p k := Real.logb_nonneg hp1 (by exact_mod_cast hk)
  refine ⟨((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1),
    k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)), ?_, ?_⟩
  · intro T io e ho y
    refine ⟨le_nuFac fun Ch X => ?_, fun halg =>
      (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) halg hp2 hdisc f k hf).2 hin⟩
    obtain ⟨hfrob, hty⟩ := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc T io X
    obtain ⟨h, hh0, -, lab, horb, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := hty y Ch f.1
    have hstep : ∀ s, InPsi H (lab (s + 1)) ↔ ¬ InPsi H (lab s) := by
      intro s
      rw [((hfrob _ _ (horb.2.1 s)).2 hin)]
      constructor
      · intro h1 h2
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H (lab s) ⟨h2, h1⟩
      · intro h1
        exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H (lab s)).resolve_left h1
    obtain ⟨hev, hpar⟩ := inPsi_orbit_parity hh0 lab hstep (by rw [horb.1]; exact hf)
    have hodd : ∀ s : ZMod h, Odd s.val → (Finset.univ.filter fun a => ty a = s).card ≤ Dw.q := by
      intro s hs
      have hn : ¬ InPsi H (lab s) := fun h1 => (Nat.not_even_iff_odd.2 hs) ((hpar s).1 h1)
      have h2 := hcard s
      rw [if_neg hn] at h2
      rw [← h2, Fintype.card_subtype]
    obtain ⟨hsat, hzero, hdep⟩ := hfr 0 f horb.1.symm
    obtain ⟨cr, -, hcr, hlow⟩ := GlobalTheory.T.detDepth_lower_bound_saturated_even_type X.C (vX_vp X) p hp (vX_vp_p X) hp3 d' h hh0 hev ty G' mu Dw.q hodd
      (0 : ZMod h) (by simp) (rk f) k hk (fun a => P.mulVec (frame Ch X f a)) hsat hzero
    rw [nuFacC, ← hdep] at *
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) hlow
    have h3 : ((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p ≤ ((rk f : ℝ) - cr) * k * p := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h4 := div_le_div_of_nonneg_right h3 hpp.le
    linarith
  · have hab : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 1 / ((p : ℝ) - 1) := by
      rw [div_le_div_iff₀ hpp (by linarith)]
      nlinarith
    have hkey : boundFine p (Dw.p + Dw.q) Dw.q (rk f) k -
        (k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) -
          (((rk f : ℝ) - Dw.q * (3 / 2 + Real.logb p k / 2)) * k * p / ((p : ℝ) ^ 2 - 1) - (rk f : ℝ) ^ 2 * (Real.logb p k + 1))) =
        (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      unfold boundFine
      push_cast
      ring
    have hpos : 0 ≤ (k : ℝ) * Dw.q * (1 / 2 * (1 / ((p : ℝ) - 1)) + (3 / 2 + Real.logb p k / 2) * (1 / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) ^ 2 - 1))) := by
      have hb : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + Real.logb p k / 2) (sub_nonneg.2 hab)
      positivity
    linarith

end GlobalTheory.RefSum

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

open Classical

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_rowsAndBand : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  intro D L P X C tf h
  have hC := h.pos
  obtain ⟨nA, nB, nC, nD, nBand⟩ := h.num
  have h3 : ¬ TwistedPlaces.InertK D 3 := h.small.2.2.2.1
  have hR : ∀ i, D.nd.l i ≠ 3 → KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = (tabX L X).len i := by
    intro i h3 hr; funext lam
    have hs : D.nd.l i ∉ D.host.small := fun e => hr.1 (Or.inl e)
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg hs, if_neg h3, if_pos hr]; rfl
  have hN : ∀ i, D.nd.l i ≠ 3 → ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = fun _ => 0 := by
    intro i h3 hr; funext lam
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg h3, if_neg hr, ite_self]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hSc := L.Sc_pos
  have hEta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hx.le _
  have hB1 : 1 ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hwB : 0 ≤ TwistedPlaces.wB L := by
    have hb' : 0 < L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X'
      positivity
    have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
    unfold TwistedPlaces.wB
    exact le_trans (by linarith) (le_max_left _ _)
  have hetaP : 0 ≤ TwistedPlaces.eta₃ L := by unfold TwistedPlaces.eta₃; linarith
  have hwP : 0 ≤ TwistedPlaces.wP L := by unfold TwistedPlaces.wP; linarith
  have hGP : 0 ≤ TwistedPlaces.GP L := by unfold TwistedPlaces.GP; linarith
  have heP : ∀ l : ℕ, l.Prime → 0 ≤ TwistedPlaces.eP L C l := by
    intro l hl
    unfold TwistedPlaces.eP
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    have h1 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := Real.logb_nonneg hl1 hB1
    have h2 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith) (by linarith)
    exact mul_nonneg hC (by linarith)
  have hflat : ∀ (tb : TwistedPlaces.Tab L) i lam (l : ℕ), 0 ≤ TwistedPlaces.flatCD L tb i lam l := by
    intro tb i lam l
    unfold TwistedPlaces.flatCD
    have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := div_nonneg (by linarith) (Nat.cast_nonneg _)
    have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if tb.band i lam then 1 else 0) :=
      mul_nonneg hetaP (by split_ifs <;> norm_num)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hP
    have h5 := hP.1
    have h3' : D.nd.l i ≠ 3 := by omega
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nA i hi hP
    · rw [hN i h3' hr]
      have hl := (D.nd.lPrime i).out
      have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
        unfold TwistedPlaces.sumOver; simp
      rw [h0, mul_zero]
      unfold TwistedPlaces.sumOver
      apply finsum_nonneg; intro lam; apply finsum_nonneg; intro _
      exact mul_nonneg (by positivity) (heP _ hl)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nB i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl1 : (1 : ℝ) ≤ D.nd.l i := by exact_mod_cast (D.nd.lPrime i).out.one_lt.le
      have h1 : 0 ≤ TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) :=
        div_nonneg (by linarith) (pow_nonneg (by linarith) _)
      have h2 : 0 ≤ (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) :=
        mul_nonneg (by linarith) (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nC i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nD i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h1)
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h2))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · exact nBand

end GlobalTheory.NLink

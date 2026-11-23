import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorRegularGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotientMinimalPrimeAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem DivisorRegularGeneric.proof (hG : FrameGraphGeneric.Statement) : DivisorRegularGeneric.Statement := by
  classical
  intro n d J u hJ hdim hu
  set L : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {linForm u} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W => hfinM.mem_toFinset
  have hevL : ∀ x : Fin n → ℂ, eval x (linForm u) = linEval u x := fun x => by
    simp [linForm, linEval, map_sum]

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one hu hW (fun h => by
      rw [hdim] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdim] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key
  choose! hh hhW hhchart using fun W (hW : W ∈ L.minimalPrimes) =>
    graphChart_of_frameGraphGeneric hG W hW.1.1 (hdimW W hW)

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin n) ℂ := fun W => ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set f : MvPolynomial (Fin n) ℂ := ∑ W ∈ T, hh W * e W with hf
  have hsplit : ∀ W ∈ T, f = hh W * e W + ∑ V ∈ T.erase W, hh V * e V := fun W hW =>
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, hh V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV => Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hfW : ∀ W ∈ L.minimalPrimes, f ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hhW W hW h
    · exact heW W hW h

  have hcomp : ∀ x ∈ zeroSet J, linEval u x = 0 → ∃ W ∈ L.minimalPrimes, x ∈ zeroSet W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp => RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hevL] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp => RingHom.mem_ker.mp (hWx hp)⟩
  have hcompInv : ∀ W ∈ L.minimalPrimes, ∀ x ∈ zeroSet W, x ∈ zeroSet J ∧ linEval u x = 0 := by
    intro W hW x hx
    refine ⟨fun p hp => hx p (hW.1.2 (Ideal.mem_sup_left hp)), ?_⟩
    rw [← hevL]
    exact hx _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  refine ⟨L ⊔ Ideal.span {f}, le_sup_left, ringKrullDim_quotient_sup_span_lt hfW hdimW, ?_⟩
  intro q hqJ hqu hqI
  obtain ⟨W, hW, hqW⟩ := hcomp q hqJ hqu
  have hfq : eval q f ≠ 0 := by
    intro h0
    refine hqI fun p hp => ?_
    have hle : L ⊔ Ideal.span {f} ≤ RingHom.ker (eval q) := by
      refine sup_le (fun p hp => ?_) (Ideal.span_le.mpr (by simpa using h0))
      obtain ⟨V, hV, hqV⟩ := hcomp q hqJ hqu
      exact RingHom.mem_ker.mpr (hqV p (hV.1.2 hp))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add, hqW _ (hrest W hW), add_zero, map_mul] at hfq
  refine graphChart_of_eq_on_open (U := {x | eval x (e W) ≠ 0})
    (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const) (right_ne_zero_of_mul hfq) ?_
    (hhchart W hW q hqW (left_ne_zero_of_mul hfq))
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxu⟩, hxe⟩
    refine ⟨?_, hxe⟩
    obtain ⟨V, hV, hxV⟩ := hcomp x hxJ hxu
    by_cases hVW : V = W
    · exact hVW ▸ hxV
    · exact absurd (hxV _ (heV W hW V hV (Ne.symm hVW))) hxe
  · rintro ⟨hxW, hxe⟩
    exact ⟨hcompInv W hW x hxW, hxe⟩

end

end GroundTheory.Heights₂.Heights

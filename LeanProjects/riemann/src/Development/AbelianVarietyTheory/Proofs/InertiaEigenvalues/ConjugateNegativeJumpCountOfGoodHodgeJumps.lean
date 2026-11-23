import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultisetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbeddingStatement

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem card_filter_nonneg_add_reflect (t : ℤ) (ht : 0 ≤ t) (M : Multiset ℤ) (h : ∀ a ∈ M, a < -1 ∨ t < a) :
    Multiset.card (M.filter (0 ≤ ·)) + Multiset.card ((M.map (fun a => t - 1 - a)).filter (0 ≤ ·)) =
      Multiset.card M := by
  rw [Multiset.filter_map, Multiset.card_map]
  have e : M.filter ((fun a => 0 ≤ a) ∘ fun a => t - 1 - a) = M.filter (fun a => ¬ 0 ≤ a) := by
    apply Multiset.filter_congr
    intro a ha
    have := h a ha
    simp only [Function.comp_apply]
    omega
  rw [e, ← Multiset.card_add, Multiset.filter_add_not]

theorem negCount_of_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  intro D bkP i s ι J hH hJ hG v v' hv hv' τ τ' hc
  obtain ⟨τc, h1, h2⟩ := GlobalTheory.T.exists_complex_reading_local_embedding D bkP i ι v hv τ
  have h2' := h2 v' hv' τ' hc
  obtain ⟨a1, a2⟩ := GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset D bkP i s v hv τ (J τc) hH (hJ v hv τ τc h1)
  obtain ⟨b1, b2⟩ := GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset D bkP i s v' hv' τ' (J (τc.comp (cj D))) hH (hJ v' hv' τ' _ h2')
  obtain ⟨g1, g2, g3⟩ := hG τc
  have k := card_filter_nonneg_add_reflect (D.R.t : ℤ) (by positivity) (J τc) g3
  rw [a1, a2, b1, b2, g2, Multiset.card_map]
  omega

end GlobalTheory.TripleGal

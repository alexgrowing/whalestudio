import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem pure_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → ∃ ι, Pure i s ι := by
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, -⟩
  refine ⟨ι, fun v hl hS A hAv σ hσ z hz => ?_⟩
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have hp : v ∉ D.ntw.pD i := fun hk => hS ⟨Or.inr (Finset.mem_coe.2 hk), hl⟩
  have hu := hR.unr v hg hp
  have hf := hA.frob v hl hu A σ hAv hσ
  have ht := (D.naut.tempered_unr _ hu).1 (hA.temp v hl)
  rw [Tgl_coe] at hf
  rw [hf, D.naut.frobEig_tw _ _ hu, IsRoot.def, eval_multiset_prod, Multiset.prod_eq_zero_iff] at hz
  simp only [Multiset.mem_map] at hz
  obtain ⟨_, ⟨_, ⟨α, hα, rfl⟩, rfl⟩, h0⟩ : ∃ p, (∃ β, (∃ α, α ∈ D.naut.frobEig (D.naut.locG π v) ∧
      α * ((normV v : ℕ) : ℂ) ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ) = β) ∧ Polynomial.X - C β = p) ∧ eval z p = 0 := hz
  have hpos : 0 < normV v := by
    have : Finite (𝓞 D.host.E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    exact Nat.card_pos
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at h0
  rw [h0, norm_mul, ht α hα, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.ofReal_re]

end GlobalTheory.TripleGal

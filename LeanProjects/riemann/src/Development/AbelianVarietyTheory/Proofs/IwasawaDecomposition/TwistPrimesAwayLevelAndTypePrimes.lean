import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwistPrimes

open GlobalTheory.Mem.LevTwist ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem twist_primes_away : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  intro B X I h
  refine ⟨I.twistPrimes_reference_tuple_eq_empty, fun u a P hP => ?_⟩
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hg := good_of_mem h (I.Q_subset_SQ a hP)
  have hS := hg.2.2.2
  have hu : (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := (under_eq_iff B.host P _).2 (Or.inr rfl)
  have hT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      ((B.primes X).T u : 𝓞 B.host.E) ∉ R.asIdeal := fun R hR hm => hS (by
    rw [← hR, (ReadTwist.plc_under_eq_iff (F := B.host.F) R (hPr.T_prime u)).2 hm]
    exact h.T_mem u)
  have hpi : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      (B.primes X).piT u ∉ R.asIdeal := fun R hR hm => hT R hR (by
    rw [← hPr.piT_norm u]; exact Ideal.mul_mem_right _ _ hm)
  have h0 : (B.primes X).piT u ≠ 0 := fun e => by
    have := hPr.piT_norm u
    rw [e, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hvT : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vT u := fun R hR hm => hpi R hR ((mem_divs h0 _).1 hm)
  have hvG : ∀ R : HeightOneSpectrum (𝓞 B.host.E), R.under (𝓞 B.host.F) = P.under (𝓞 B.host.F) →
      R ∉ (B.primes X).vGs := fun R hR hm => hS (by rw [← hR]; exact plc_mem h hm)
  refine ⟨⟨hvT P rfl, hvG P rfl, hvT _ hu, hvG _ hu, fun hc => ?_⟩, hpi P rfl, fun hm => hT P rfl ?_⟩
  · have e := (good_of_mem h (I.Q_subset_SQ a hc)).1
    rw [hu, hg.1] at e
    exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 hg.2).1 e.symm
  · rw [← map_natCast (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))]
    exact hm

end GlobalTheory.Mem.Col2.TwistPrimes

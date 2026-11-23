import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idemAt_eq_split {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
  have key : ∀ f : AE D, Formalism.L2.NTheta.IsIdemAt f P → f = e₀ := by
    intro f hf
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 f hf.1.1 hf.1.2.1 (below_of_idemAt hf) with h | h
    · exact h
    exfalso
    exact hP (conj_of_cA he₀ hf h)
  rw [key e he, key e' he']

theorem idem_orth {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : P ≠ Q) : e * e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : e' * phiE (belowPl Q) 1 = e' := by rw [← hs', mul_add, he'.1.1, he'.1.2.1, add_zero]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · exfalso
      apply hPQ
      apply HeightOneSpectrum.ext
      ext x
      by_cases hx0 : x = 0
      · subst hx0; simp only [zero_mem]
      rw [he.2 x hx0, he'.2 x hx0, h0, h]
    · rw [h, h0]; exact he₀.1.2.1
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (e' * phiE (belowPl Q) 1) = e * e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem idem_orth_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : ¬ Lev.IsConjPl (D := D) P Q) :
    e * cA D e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : cA D e' * phiE (belowPl Q) 1 = cA D e' := by
    rw [← hs', mul_add, mul_comm (cA D e') e', he'.1.2.1, zero_add, ← map_mul, he'.1.1]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · rw [h, h0]; exact he₀.1.2.1
    · exfalso
      exact hPQ (conj_of_cA he he' (h.trans (congrArg (cA D) h0.symm)))
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (cA D e' * phiE (belowPl Q) 1) =
        e * cA D e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem not_two_primes {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpI : (p : 𝓞 D.host.E) ∈ I) (hqI : (q : 𝓞 D.host.E) ∈ I) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply hI
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact add_mem (I.mul_mem_left _ hpI) (I.mul_mem_left _ hqI)

theorem nat_mem_of_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : Lev.IsConjPl (D := D) P Q) {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨c, hc, hce⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    show (c : D.host.E) = ((n : 𝓞 D.host.E) : D.host.E)
    rw [hce]; push_cast; exact star_natCast n
  rwa [← this]

theorem char_mem {P : HeightOneSpectrum (𝓞 D.host.E)} {q : ℕ} (hq : q.Prime)
    (hc : Nat.card (Formalism.L2.DIV.kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  have hfin : Finite (Formalism.L2.DIV.kP P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hq.ne_zero)
  have h0 : (Nat.card (Formalism.L2.DIV.kP P)) • (1 : Formalism.L2.DIV.kP P) = 0 := card_nsmul_eq_zero'
  rw [hc, nsmul_one] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h0

end Formalism.IndefR.Fin

end

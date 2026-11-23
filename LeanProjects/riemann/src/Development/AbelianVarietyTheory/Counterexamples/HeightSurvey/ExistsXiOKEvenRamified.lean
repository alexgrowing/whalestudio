import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral

noncomputable section

namespace GlobalTheory.XiCounterexample

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.FinalJoin
open GlobalTheory.NormOneChar
open scoped TensorProduct

theorem conj_emb (D : D7) (φ : D.host.E →+* ℂ) (y : D.host.E) :
    φ (GlobalTheory.Member.cF D y) = starRingEnd ℂ (φ y) :=
  @IsCMField.complexEmbedding_complexConj D.host.E _ _
    (D.host.isCMField_hostE) _ φ y

theorem conj_conj (D : D7) (y : D.host.E) : GlobalTheory.Member.cF D (GlobalTheory.Member.cF D y) = y :=
  D.host.φ₀.injective (by rw [conj_emb, conj_emb, Complex.conj_conj])

theorem mem_congOne (D : D7) (N : ℕ) (x : (AfE D)ˣ) :
    x ∈ congOne (GlobalTheory.Member.cF D) N ↔ CongOne N x ∧ NormOne x := by
  unfold CongOne
  simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
  exact Iff.rfl

theorem fin_of_rat_tame (D : D7) (N : ℕ) (hN : 0 < N) (xi : (AfE D)ˣ →* ℂˣ)
    (h1 : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → xi x = 1)
    (h2 : ∀ x, NormOne x → CongOne N x → xi x = 1) : ∃ m : ℕ, 0 < m ∧ ∀ x, NormOne x → xi x ^ m = 1 := by
  obtain ⟨m, hm, hexp⟩ := exists_exponent (GlobalTheory.Member.cF D) (conj_conj D) N hN
  refine ⟨m, hm, fun x hn => ?_⟩
  rw [← map_pow]
  obtain ⟨r, ⟨⟨a, ha⟩, hr⟩, k, hk, e⟩ := Subgroup.mem_sup.1 (hexp x hn)
  rw [← e, map_mul, h1 r a ha hr, h2 k ((mem_congOne D _ _).1 hk).2 ((mem_congOne D _ _).1 hk).1, mul_one]

end GlobalTheory.XiCounterexample

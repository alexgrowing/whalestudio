import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.BadPrimesS

open GlobalTheory.ColNorms.BadPrimes

theorem bad_primes_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ P ∈ rowSG Pr sel mu, P ∈ Pr.vGs) ∧ (∀ P ∈ Pr.vGs, ∃ i, P ∈ Pr.vG i ∧ Formalism.L2.Col.qOf P = Pr.g i ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ ((Pr.g (1 - i) : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ Pr.piT u ∉ P.asIdeal) ∧ (∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal) ∧ (∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) = (Pr.g 0 * Pr.g 1) ^ N.R.f ∧ Odd (Pr.T u) ∧ (∀ i, Odd (Pr.g i)) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (2 : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h
  obtain ⟨⟨-, -, -, -, -, -, hX1, -, -, hPr, -, hc, -, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  have hX := hX1.ok
  have h2 : 2 ∣ Pr.cond := by
    rw [hc, NumDatum.cond]
    exact N.H.toHostRaw.two_dvd_condN
  have hS : ∀ P, P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u ↔ P ∈ Pr.vT u ∨ P ∈ Pr.vGs := fun P => by
    rw [← rowSG_one sel Sg]
    exact Finset.mem_union
  refine ⟨fun P hP => rowSG_one sel Sg ▸ hP, fun P hP => ?_, fun P hP => T_mem hPr hP, ?_, odd_typePrime_of_two_dvd_cond hX hPr h2 u,
    odd_g hPr h2, fun P hP => ⟨fun h' => conjP_notMem hPr u ((hS _).1 hP) ((hS _).1 h'), ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_vG hP
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun hT =>
      hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i) hT (g_mem hPr hi))
    refine ⟨i, hi, hPr.vG_norm i P hi, g_mem hPr hi,
      (GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi).2, fun hg => ?_, hT,
      fun hπ => hT (hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ hπ)⟩
    have := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime _) (hPr.g_prime _) hg (g_mem hPr hi))
    fin_cases i <;> simp at this
  · rw [Finset.prod_coe_sort _ (fun P => Formalism.L2.Col.qOf P), rowSG_one, prod_qOf_vGs hPr,
      GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm]
  · rcases (hS _).1 hP with h | h
    · exact two_notMem_vT hPr h2 h
    · obtain ⟨i, hi⟩ := exists_vG h
      intro hP2
      have := eq_of_natCast_mem P (hPr.g_prime i) Nat.prime_two (g_mem hPr hi) (by exact_mod_cast hP2)
      have ho := odd_g hPr h2 i
      rw [this] at ho
      exact absurd ho (by decide)

end GlobalTheory.Core.Ht2.BadPrimesS

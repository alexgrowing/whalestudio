import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.Proof.AbsNormSplitPlace

open GlobalTheory.Proof.NarrowJetMoments

theorem absNorm_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hl : (Ideal.absNorm v.asIdeal).Prime)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨Q, Q', -, hm⟩ := hs
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap]
    congr 1
    rw [← h2]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
  have h1 : ∀ R : HeightOneSpectrum (𝓞 E), Ideal.absNorm R.asIdeal ≠ 1 := fun R h =>
    R.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hb := (hl.mul_eq_prime_sq_iff (h1 Q) (h1 Q')).1 hN
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP, Ideal.under_def]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · rw [← Q.isMaximal.eq_of_le P.isPrime.ne_top h, hb.1]
  · rw [← Q'.isMaximal.eq_of_le P.isPrime.ne_top h, hb.2]

theorem plc_eq_absNorm {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (hl : (Ideal.absNorm v.asIdeal).Prime) : ringChar (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  haveI := v.isPrime
  exact ((Nat.dvd_prime hl).1 h6).resolve_left CharP.ringChar_ne_one

theorem main : ∀ (Z : Dat) (u : Z.Pr.Word) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S), Z.Ok → IsSel Z.X sel → Z.Pr.T u ∈ S → (∀ i, Z.Pr.g i ∈ S) → (∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u) ∧ ∀ P ∈ rowSG Z.Pr sel mu, (Formalism.L2.Col.qOf P).Prime ∧ Formalism.L2.Col.qOf P ≠ Z.Pr.T u ∧ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
  intro Z u sel S mu hZ hsel hT hg
  have hPr := hZ.primes
  have hTn : ∀ P ∈ rowSG Z.Pr sel mu, ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  refine ⟨fun P hP hP' => ?_, fun P hP => ?_⟩
  · rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
    · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
      change cO Z.X.E (Z.Pr.piT u) ∈ (conjPrime₂ P).asIdeal
      rw [mem_conjP, cO_cO]
      exact decoFin_mem_of_mem_divs h
    · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
    · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
    · exact conjP_notMem_rowSG hZ.fields hPr hsel hg h h'
  · have key : (Formalism.L2.Col.qOf P).Prime ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
      classical
      rcases Finset.mem_union.1 hP with h | h
      · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
        have e : Formalism.L2.Col.qOf P = Z.Pr.g i := hPr.vG_norm i P hi
        exact ⟨e ▸ hPr.g_prime i, Or.inl ⟨i, e⟩⟩
      · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
        have e1 : Formalism.L2.Col.qOf P = Ideal.absNorm v.asIdeal :=
          absNorm_of_split hZ.fields.rankE hv.1 hv.2.1.1 (e ▸ hsel v)
        refine ⟨e1 ▸ hv.2.1.1, Or.inr ?_⟩
        rw [e1, ← plc_eq_absNorm hv.2.1.1]
        exact hv.2.2
    refine ⟨key.1, fun e => hTn P hP ?_, hTn P hP, key.2⟩
    rw [← e]
    exact Ideal.absNorm_mem _

end GlobalTheory.Proof.AbsNormSplitPlace

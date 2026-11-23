import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.BadPrimes

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_cofactor {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal := by
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hP]
  rcases P.isPrime.mul_le.1 hle with h | h
  · have : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q', hQ, hm⟩
  · have : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q, hQ.symm, hm.trans (mul_comm _ _)⟩

theorem absNorm_eq_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hq : (Ideal.absNorm v.asIdeal).Prime) {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨P', -, hm⟩ := exists_cofactor hs hP
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E), ← h2,
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E]
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hP2 : Ideal.absNorm P'.asIdeal ≠ 1 := fun h => P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact (((Nat.Prime.mul_eq_prime_sq_iff hq hP1 hP2).1 h1)).1

theorem notMem_sq_of_split {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {a : 𝓞 F} (ha : a ∉ v.asIdeal ^ 2)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  intro hm2
  obtain ⟨P', hne, hm⟩ := exists_cofactor hs hP
  have hav : a ∈ v.asIdeal := by
    rw [← hP, Ideal.under_def, Ideal.mem_comap]
    exact Ideal.pow_le_self two_ne_zero hm2
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 hav
  have h1 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) J) := by
    rw [← mul_assoc, ← hm, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, Ideal.dvd_span_singleton, ← sq]
    exact hm2
  have h3 := (mul_dvd_mul_iff_left P.ne_bot).1 h1
  rcases P.prime.dvd_or_dvd h3 with h | h
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top (Ideal.le_of_dvd h))).symm
  · have h4 : J ≤ v.asIdeal := by
      rw [← hP, Ideal.under_def, ← Ideal.map_le_iff_le_comap]
      exact Ideal.le_of_dvd h
    apply ha
    rw [← Ideal.span_singleton_le_iff_mem, hJ, sq]
    exact Ideal.mul_mono_right h4

end Split

open GlobalTheory.Proof.NarrowJetMoments in

theorem bad_primes : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ (((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u) := by
  classical
  intro X Pr sel S mu u hX hPr hsel hT hg P hP
  have hoff : ∀ Q ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hQ
  have hmem : ∀ Q, Q ∈ Sall sel mu u ↔ Q ∈ Pr.vT u ∨ Q ∈ rowSG Pr sel mu := fun Q => by
    unfold Sall
    exact Finset.mem_union
  rcases (hmem P).1 hP with h | h
  · have hTP := T_mem hPr u ⟨P, h⟩
    refine ⟨fun hc => ?_, ?_, ?_, fun _ => h, fun _ => hTP⟩
    · rcases (hmem _).1 hc with h' | h'
      · apply conj_piT_notMem hPr u ⟨P, h⟩
        exact (mem_conjP P _).1 (decoFin_mem_of_mem_divs h')
      · exact hoff _ h' (natCast_mem_conjP.2 hTP)
    · rw [hPr.vT_norm u P h]
      exact hPr.T_prime u
    · rw [hPr.vT_norm u P h]
      exact (T_unif hX hPr u ⟨P, h⟩).2
  · have hn := hoff P h
    refine ⟨fun hc => ?_, ?_⟩
    · rcases (hmem _).1 hc with h' | h'
      · exact hn (natCast_mem_conjP.1 (T_mem hPr u ⟨_, h'⟩))
      · exact conjP_notMem_rowSG hX hPr hsel hg h h'
    have hlast : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u :=
      ⟨fun h' => absurd h' hn, fun h' => T_mem hPr u ⟨P, h'⟩⟩
    rcases Finset.mem_union.1 h with h1 | h1
    · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h1
      rw [hPr.vG_norm i P hi]
      refine ⟨hPr.g_prime i, ?_, hlast⟩
      have hrk : 2 * X.f = Module.finrank ℚ X.E := by
        rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
        rfl
      have hcc : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
      refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E (cO X.E) (X.conjO (Pr.piG i)) (Pr.g i) cO_cO (hPr.g_prime i) ?_ ?_ ?_
        (hPr.vG_norm i) P hi
      · rw [hcc, mul_comm, hPr.piG_norm i]
      · rw [hcc]
        exact (hPr.piG_cop i).symm
      · rw [← hrk, ← hPr.vG_card i]
        rfl
    · obtain ⟨v, ⟨hs, ⟨hq, hq2⟩, -⟩, rfl⟩ := good_of_mem_QE h1
      rw [absNorm_eq_of_split hX.rankE hs hq (hsel v)]
      refine ⟨hq, ?_, hlast⟩
      have := notMem_sq_of_split hs hq2 (hsel v)
      rwa [map_natCast] at this

end GlobalTheory.ThetaMove.BadPrimes

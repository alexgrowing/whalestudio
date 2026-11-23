import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Formalism.LocalToGlobal.Columns.ChainInst

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mq_finrank : Module.finrank (𝓞 F) (𝓞 E) = Module.finrank F E :=
  (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

theorem mq_nat {q a b : ℕ} (hq : q.Prime) (h : a * b = q ^ 2) (ha : a ≠ 1) (hb : b ≠ 1) : a = q := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro b h)
  interval_cases k
  · exact absurd (pow_zero q) ha
  · exact pow_one q
  · exfalso
    apply hb
    have h0 : 0 < q ^ 2 := pow_pos hq.pos 2
    exact Nat.eq_of_mul_eq_mul_left h0 (by rw [h, mul_one])

theorem mq_absNorm (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (hq : (Ideal.absNorm v.asIdeal).Prime) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  have h := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) v.asIdeal
  rw [hv, map_mul, mq_finrank, h2] at h
  exact mq_nat hq h (fun h1 => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)) (fun h1 => P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1))

theorem mq_notMem_sq {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) {q : 𝓞 F} (hq : q ∈ v.asIdeal) (hq2 : q ∉ v.asIdeal ^ 2) :
    algebraMap (𝓞 F) (𝓞 E) q ∉ P.asIdeal ^ 2 := by
  intro hc
  have hs := qe_sup v q hq hq2
  have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal ^ 2 := by
    rw [← hs, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, hv]
    refine sup_le ((Ideal.span_singleton_le_iff_mem _).2 hc) ?_
    rw [mul_pow]
    exact (Ideal.mul_le_left : P.asIdeal ^ 2 * P'.asIdeal ^ 2 ≤ P.asIdeal ^ 2)
  rw [hv, pow_two] at h1
  have h3 : P.asIdeal * P.asIdeal ∣ P.asIdeal * P'.asIdeal := Ideal.dvd_iff_le.2 h1
  have h4 : P.asIdeal ∣ P'.asIdeal := (mul_dvd_mul_iff_left P.ne_bot).1 h3
  exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top (Ideal.dvd_iff_le.1 h4)).symm)

theorem mq_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (hd : DegOne v) :
    ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  rw [mq_absNorm h2 hv hd.1]
  have h := mq_notMem_sq hne hv (Ideal.absNorm_mem v.asIdeal) hd.2
  rwa [map_natCast] at h

end Gen

theorem mq_rowSG_unif {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) :
    ∀ P : rowSG Pr sel mu, ((Col.qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 := by
  classical
  rintro ⟨P, hP⟩
  rcases Finset.mem_union.1 hP with h | h
  · exact ciQ_notMem_sq hX hPr h
  · obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).mp h
    obtain ⟨⟨P1, P2, hne, hsp⟩, hd, -⟩ := mu.good hv
    show ((Ideal.absNorm (sel v).asIdeal : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal ^ 2
    by_cases h1 : sel v = P1
    · rw [h1]; exact mq_split hX.rankE hne hsp hd
    · by_cases h2 : sel v = P2
      · rw [h2]; exact mq_split hX.rankE hne.symm (by rw [hsp, mul_comm]) hd
      · exact absurd (hsel v) (d_other hsp h1 h2)

end Formalism.L2.Ker

import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.NotSmallIso

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.AAUnitAway

theorem natCast_notMem {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))

theorem exists_den (D : D7) (Q : Ideal (𝓞 D.host.E)) [hQ : Q.IsPrime] {l : ℕ} (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hlQ : (l : 𝓞 D.host.E) ∈ Q) :
    ∃ z : 𝓞 D.host.E, z ∉ Q ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * (z : D.host.E) := by
  have hnot : ¬ D.host.𝔟 ≤ Q := by
    intro hle
    have hd : Q ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := by
      rw [D.host.𝔟_spec.1]
      exact (Ideal.dvd_iff_le.2 hle).mul_right _
    exact natCast_notMem hQ.ne_top hlQ (Nat.Coprime.mul_left
      ((Nat.Prime.coprime_iff_not_dvd hl).2 (UpperTheory.Small.not_dvd_QS D.host hl h2)).symm
      ((Nat.coprime_primes D.host.hyp.1 hl).2 hq.symm)) (D.host.der.diffSupport Q hQ hd)
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  refine ⟨z, hzP, fun t ha => ?_⟩
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  exact ⟨w, hw⟩

theorem localization_le_of_le_localization₂ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {I J : Submodule (𝓞 E) E}
    (h : I ≤ localization₂ P.asIdeal J) : localization₂ P.asIdeal I ≤ localization₂ P.asIdeal J := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP P I x).1 hx
  obtain ⟨t, ht, hx⟩ := (mem_locP P J _).1 (h hx)
  refine (mem_locP P J x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases P.isPrime.mem_or_mem hm with h | h
  exacts [ht h, hs h]

theorem locP_AA (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ) (hl : l.Prime) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q)
    (hP : (l : 𝓞 X.E) ∈ P.asIdeal) (hc : Nat.Coprime (Ideal.absNorm cc) l) :
    localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  haveI := P.isPrime
  refine le_antisymm (localization_le_of_le_localization₂ P ?_) (localization_le_of_le_localization₂ P ?_)
  · obtain ⟨z, hz, hden⟩ := exists_den D (P.asIdeal.comap j) hl h2 hq (by rw [Ideal.mem_comap, map_natCast]; exact hP)
    refine Submodule.span_le.2 ?_
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine (mem_locP P _ _).2 ⟨j z, hz, Submodule.mem_one.2 ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    rw [e, hw]
    ring
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
    refine (mem_locP P _ _).2 ⟨(Ideal.absNorm cc : ℕ), natCast_notMem P.isPrime.ne_top hP hc, ?_⟩
    have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
      refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
      simp
    convert Submodule.smul_mem _ y h1 using 1
    simp [Algebra.smul_def, mul_comm]

theorem sq_ne_neg {X : Fields} (hX : X.Ok) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f) (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p)
    (a : X.E) : a ^ 2 ≠ -(p : X.E) := by
  intro ha
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hint : IsIntegral ℤ a := by
    refine IsIntegral.of_pow two_pos ?_
    rw [ha]
    exact (isIntegral_algebraMap (R := ℤ) (x := (p : ℤ)) |>.neg) |> fun h => by simpa using h
  obtain ⟨b, hba⟩ : ∃ b : 𝓞 X.E, algebraMap (𝓞 X.E) X.E b = a := ⟨⟨a, hint⟩, rfl⟩
  have hb : b ^ 2 = -(p : 𝓞 X.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hba, ha, map_neg, map_natCast]
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  have haP : b ∈ P.asIdeal :=
    P.isPrime.mem_of_pow_mem 2 (hb ▸ P.asIdeal.neg_mem hpP)
  refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP ?_
  have := Ideal.pow_mem_pow haP 2
  rwa [hb, neg_mem_iff] at this

theorem notMem_small {X : Fields} (hX : X.Ok) (D : D7) (s : Seam D X) (π : 𝓞 X.E) (p : ℕ) (hp : p.Prime)
    (hn : π * X.conjO π = (p : 𝓞 X.E)) (hcop : IsCoprime π (X.conjO π)) (hcard : (divs π).card = X.f)
    (hN : ∀ P ∈ divs π, Ideal.absNorm P.asIdeal = p) : p ∉ D.host.small := by
  intro hs
  have hrk : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P, hP⟩ := Finset.card_pos.1 (hcard ▸ hX.f_pos)
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hN P hP ▸ Ideal.absNorm_mem _
  exact (UpperTheory.Ram.not_dvd_QS_of_notMem_sq D.host.toHostAx D.host.QS_exact X.E s.iE P p hp hpP
    (GlobalTheory.SplitUnram.natCast_notMem_sq X.E X.conjO π p hcc hp hn hcop (by rw [hrk, hcard]) hN P hP)).1
    (Nat.dvd_of_mem_primeFactors hs)

theorem primes_ne (Z : Dat) (D : D7) (s : Seam D Z.X) (hZ : Z.Ok) :
    (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q := by
  have ha : (s.iE.symm (D.host.sqq)) ^ 2 = -(D.host.q : Z.X.E) := by
    rw [← map_pow, D.host.sqq_sq, map_neg, map_natCast]
  have hcc : ∀ x, Z.X.conjO (Z.X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : Z.X.E))
  have hPr := hZ.primes
  refine ⟨fun u => ⟨fun h => ?_, fun h => ?_⟩, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact notMem_small hZ.fields D s _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) h
  · exact sq_ne_neg hZ.fields _ _ (hPr.T_prime u) (hPr.piT_norm u) (hPr.piT_cop u) (hPr.vT_card u) (hPr.vT_norm u) _ (h ▸ ha)
  · exact notMem_small hZ.fields D s (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) h
  · exact sq_ne_neg hZ.fields (Z.X.conjO (Z.Pr.piG i)) _ (hPr.g_prime i) (by rw [hcc, mul_comm, hPr.piG_norm i])
      (by rw [hcc]; exact (hPr.piG_cop i).symm) (hPr.vG_card i) (hPr.vG_norm i) _ (h ▸ ha)

theorem locP_AA_and_primes_ne : (∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)) (l : ℕ), l.Prime → l ∉ D.host.small → l ≠ D.host.q → (l : 𝓞 X.E) ∈ P.asIdeal → Nat.Coprime (Ideal.absNorm cc) l → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) ∧ ∀ (Z : Dat) (D : D7) (s : Seam D Z.X), Z.Ok → (∀ u, Z.Pr.T u ∉ D.host.small ∧ Z.Pr.T u ≠ D.host.q) ∧ ∀ i, Z.Pr.g i ∉ D.host.small ∧ Z.Pr.g i ≠ D.host.q :=
  ⟨locP_AA, primes_ne⟩

end GlobalTheory.AAUnitAway

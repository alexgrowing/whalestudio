import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace GlobalTheory.GO.SplitGlue

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in

theorem exists_smul_le {N N' : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hN' : Submodule.IsLattice E N') : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ x ∈ N', a • x ∈ N := by
  classical
  have h0 : ∀ x : Sp E n, ∃ a : 𝓞 E, a ≠ 0 ∧ a • x ∈ N := by
    intro x
    have hx : x ∈ Submodule.span E (N : Set (Sp E n)) := hN.span_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (N : Set (Sp E n)) x hx
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  obtain ⟨s, rfl⟩ := hN'.fg
  choose a ha0 ha using h0
  refine ⟨∏ y ∈ s, a y, Finset.prod_ne_zero_iff.mpr fun y _ => ha0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ hy, mul_smul]
    exact N.smul_mem _ (ha y)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy

omit [StarRing E] in

theorem mem_of_forall (N : Submodule (𝓞 E) (Sp E n)) {x : Sp E n}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), ∃ s ∉ w.asIdeal, s • x ∈ N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 E) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x) := h1 ▸ Submodule.mem_top
    exact hx (by simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
  exact hs (hle (by simpa using hsx))

omit [StarRing E] in

theorem eq_of_sameAt {N N' : Submodule (𝓞 E) (Sp E n)} (h : ∀ w, SameAt w N N') : N = N' := by
  apply le_antisymm
  · intro x hx
    refine mem_of_forall N' fun w => ?_
    obtain ⟨_, _, a', ha', _, h2⟩ := h w
    exact ⟨a', ha', h2 x hx⟩
  · intro x hx
    refine mem_of_forall N fun w => ?_
    obtain ⟨a, ha, _, _, h1, _⟩ := h w
    exact ⟨a, ha, h1 x hx⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

omit [NumberField E] [StarRing E] in
theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', h3, h4⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h3 x hx)
  · rw [mul_smul]; exact h4 _ (h2 x hx)

theorem conjP_conjP (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem sameAt_dual {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt (conjPrime₂ Q) (dual (hStd E n) N) (dual (hStd E n) N') := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨cO E a', by rwa [mem_conjP, cO_cO], cO E a, by rwa [mem_conjP, cO_cO], fun x hx => ?_, fun x hx => ?_⟩
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h2 y hy)
  · rw [mem_dual] at hx ⊢
    intro y hy
    rw [← hStd_osmul_left]
    exact hx _ (h1 y hy)

theorem exists_glue {L L' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L')
    (P : HeightOneSpectrum (𝓞 E)) : ∃ L'' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E L'' ∧ SameAt P L' L'' ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q L L'' := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_smul_le hL hL'
  obtain ⟨b, hb0, hb⟩ := exists_smul_le hL' hL
  have hI : Ideal.span {a * b} ≠ ⊥ := by simpa using ⟨ha0, hb0⟩
  obtain ⟨J, hJ, hdJ⟩ := Ideal.eq_prime_pow_mul_coprime hI P.asIdeal (hpm := P.isMaximal)
  generalize Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a * b})) = k at hdJ
  have hdvd : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∃ c, r * s = c * (a * b) := by
    intro r hr s hs
    have := Ideal.mul_mem_mul hr hs
    rw [← hdJ, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  have h1 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L, (r * s) • x ∈ L' := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, ← mul_assoc, mul_smul]
    exact L'.smul_mem _ (hb x hx)
  have h2 : ∀ r ∈ P.asIdeal ^ k, ∀ s ∈ J, ∀ x ∈ L', (r * s) • x ∈ L := by
    intro r hr s hs x hx
    obtain ⟨c, hc⟩ := hdvd r hr s hs
    rw [hc, mul_comm a b, ← mul_assoc, mul_smul]
    exact L.smul_mem _ (ha x hx)
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ P.asIdeal := by
    by_contra H
    push Not at H
    have : P.asIdeal ⊔ J ≤ P.asIdeal := sup_le le_rfl H
    rw [hJ] at this
    exact P.isPrime.ne_top (top_le_iff.1 this)
  have hs0 : s ≠ 0 := by rintro rfl; exact hsP P.asIdeal.zero_mem
  let L'' : Submodule (𝓞 E) (Sp E n) := J • L' ⊔ (P.asIdeal ^ k) • L
  have hA : ∀ x ∈ L', s • x ∈ L'' := fun x hx => Submodule.mem_sup_left (Submodule.smul_mem_smul hsJ hx)
  have hB : ∀ x ∈ L'', s • x ∈ L' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L'.add_mem (L'.smul_mem _ (Submodule.smul_le_right hy)) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]; exact h1 r hr s hsJ u hu
    · rw [smul_add]; exact L'.add_mem hu hv
  refine ⟨L'', ?_, ⟨s, hsP, s, hsP, hB, hA⟩, fun Q hQ => ?_⟩
  · have hsup : Submodule.IsLattice E (L' ⊔ L) :=
      ⟨hL'.fg.sup hL.fg, by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono (le_sup_right : L ≤ L' ⊔ L)⟩
    exact lattice_of_smul hL' hsup (sup_le_sup Submodule.smul_le_right Submodule.smul_le_right) hs0 hA
  · obtain ⟨t, htP, htQ⟩ := exists_mem_notMem hQ.symm
    have ht : t ^ k ∈ P.asIdeal ^ k := Ideal.pow_mem_pow htP k
    have ht' : t ^ k ∉ Q.asIdeal := fun h => htQ (Q.isPrime.mem_of_pow_mem k h)
    refine ⟨t ^ k, ht', t ^ k, ht', fun x hx => ?_, fun x hx => Submodule.mem_sup_right (Submodule.smul_mem_smul ht hx)⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine L.add_mem ?_ (L.smul_mem _ (Submodule.smul_le_right hz))
    refine Submodule.smul_induction_on hy (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul]; exact h2 _ ht r hr u hu
    · rw [smul_add]; exact L.add_mem hu hv

theorem exists_selfDual_prescribed (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (N M : Submodule (𝓞 E) (Sp E n)) (Q : HeightOneSpectrum (𝓞 E)) (hQ : conjPrime₂ Q ≠ Q) (hN : Submodule.IsLattice E N)
    (hu : IsUnimodular (hStd E n) N) (hM : Submodule.IsLattice E M) :
    ∃ N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N' ∧ IsUnimodular (hStd E n) N' ∧
      localization₂ Q.asIdeal N' = localization₂ Q.asIdeal M ∧
      ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → localization₂ Q'.asIdeal N' = localization₂ Q'.asIdeal N := by
  obtain ⟨L, hL, hLQ, hLo⟩ := exists_glue hN hM Q
  obtain ⟨N', hN', hc, ho⟩ := exists_glue hL (dual_lattice hM) (conjPrime₂ Q)
  have h1 : SameAt Q M N' := sameAt_trans hLQ (ho Q hQ.symm)
  have h2 : ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q' ≠ conjPrime₂ Q → SameAt Q' N N' :=
    fun Q' a b => sameAt_trans (hLo Q' a) (ho Q' b)
  refine ⟨N', hN', ?_, h1.localization_eq, fun Q' a b => (h2 Q' a b).localization_eq⟩
  refine eq_of_sameAt fun w => ?_
  by_cases hw : w = Q
  · subst hw
    have := sameAt_dual hc
    rw [conjP_conjP, dual_dual hM] at this
    exact sameAt_trans (sameAt_symm this) h1
  by_cases hw' : w = conjPrime₂ Q
  · subst hw'
    exact sameAt_trans (sameAt_symm (sameAt_dual h1)) hc
  have := sameAt_dual (h2 (conjPrime₂ w) (fun h => hw' (by rw [← h, conjP_conjP]))
    (fun h => hw (by rw [← conjP_conjP w, h, conjP_conjP])))
  rw [conjP_conjP, show dual (hStd E n) N = N from hu] at this
  exact sameAt_trans (sameAt_symm this) (h2 w hw hw')

end GlobalTheory.GO.SplitGlue

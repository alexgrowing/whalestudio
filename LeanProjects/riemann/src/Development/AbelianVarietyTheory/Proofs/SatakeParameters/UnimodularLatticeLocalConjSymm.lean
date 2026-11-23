import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

noncomputable section

namespace GlobalTheory.GO.UniExt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

private theorem mem_localization_iff_exists_smul_mem {N : Submodule (𝓞 E) (Sp E n)} (Q : HeightOneSpectrum (𝓞 E))
    (x : Sp E n) : x ∈ localization₂ Q.asIdeal N ↔ ∃ s ∉ Q.asIdeal, s • x ∈ N := by
  unfold localization₂ locS
  exact Iff.rfl

private theorem mem_iff_hStd_integral_of_isUnimodular {N : Submodule (𝓞 E) (Sp E n)}
    (hu : IsUnimodular (hStd E n) N) (x : Sp E n) :
    x ∈ N ↔ ∀ y ∈ N, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = hStd E n y x := by
  unfold IsUnimodular dual at hu
  conv_lhs => rw [← hu]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

private theorem hStd_smul_left (a : 𝓞 E) (y z : Sp E n) :
    hStd E n (a • y) z = algebraMap (𝓞 E) E (cO E a) * hStd E n y z := by
  rw [← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂, smul_eq_mul]
  rfl

private theorem hStd_smul_right (a : 𝓞 E) (y z : Sp E n) :
    hStd E n y (a • z) = algebraMap (𝓞 E) E a * hStd E n y z := by
  rw [← algebraMap_smul E a z, map_smul, smul_eq_mul]

private theorem cO_mem_conjP_iff (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E) :
    cO E t ∈ (conjPrime₂ P).asIdeal ↔ t ∈ P.asIdeal := by
  unfold conjPrime₂
  show cO E t ∈ Ideal.comap (cO E) P.asIdeal ↔ _
  rw [Ideal.mem_comap]
  have htt : cO E (cO E t) = t := RingOfIntegers.ext (star_star (t : E))
  rw [htt]

theorem mem_localization_conj_iff {N : Submodule (𝓞 E) (Sp E n)} (hl : N.FG) (hu : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal N ↔ ∀ y ∈ localization₂ P.asIdeal N, IntAt (conjPrime₂ P) (hStd E n y x) := by
  rw [mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, hsx⟩ y hy
    obtain ⟨t, ht, hty⟩ := (mem_localization_iff_exists_smul_mem P y).1 hy
    obtain ⟨r, hr⟩ := (mem_iff_hStd_integral_of_isUnimodular hu (s • x)).1 hsx (t • y) hty
    unfold IntAt
    refine ⟨r, cO E t * s, ?_, ?_⟩
    · intro hmem
      rcases (conjPrime₂ P).isPrime.mem_or_mem hmem with h | h
      · exact ht ((cO_mem_conjP_iff P t).1 h)
      · exact hs h
    · rw [hr, hStd_smul_left, hStd_smul_right, map_mul]
      ring
  · intro H
    classical
    obtain ⟨S, hS⟩ := hl
    have hloc : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧
        ∃ r : 𝓞 E, algebraMap (𝓞 E) E s * hStd E n y x = algebraMap (𝓞 E) E r := by
      intro y hy
      have hyN : y ∈ N := hS ▸ Submodule.subset_span hy
      have hyl : y ∈ localization₂ P.asIdeal N :=
        (mem_localization_iff_exists_smul_mem P y).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by rwa [one_smul]⟩
      have hint := H y hyl
      unfold IntAt at hint
      obtain ⟨r, s, hs, h⟩ := hint
      exact ⟨s, hs, r, h⟩
    choose! u hu0 w hw using hloc
    refine ⟨∏ y ∈ S, u y, ?_, ?_⟩
    · intro hmem
      obtain ⟨y, hy, hyu⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P).isPrime)).1 hmem
      exact hu0 y hy hyu
    · rw [mem_iff_hStd_integral_of_isUnimodular hu]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        refine ⟨(∏ y ∈ S.erase z, u y) * w z, ?_⟩
        rw [hStd_smul_right, ← Finset.mul_prod_erase S u hz, map_mul, map_mul, ← hw z hz]
        ring
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨ra, hra⟩ := ha
        obtain ⟨rb, hrb⟩ := hb
        exact ⟨ra + rb, by rw [map_add, hra, hrb, map_add, LinearMap.add_apply]⟩
      | smul a z _ hz =>
        obtain ⟨rz, hrz⟩ := hz
        exact ⟨cO E a * rz, by rw [hStd_smul_left, map_mul, hrz]⟩

theorem conjP_involutive (Q : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ Q) = Q := by
  unfold conjPrime₂
  apply HeightOneSpectrum.ext
  simp only [Ideal.comap_comap]
  unfold cO
  have hid : (RingOfIntegers.mapRingHom (starRingEnd E)).comp
      (RingOfIntegers.mapRingHom (starRingEnd E)) = RingHom.id (𝓞 E) :=
    RingHom.ext fun x => RingOfIntegers.ext (star_star (x : E))
  rw [hid, Ideal.comap_id]

theorem le_of_forall_localized_eq {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N') : N ≤ N' := by
  intro x hx
  by_contra hnx
  let I : Ideal (𝓞 E) := N'.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x)
  have hI : I ≠ ⊤ := by
    intro htop
    apply hnx
    have h1 : (1 : 𝓞 E) ∈ I := htop ▸ Submodule.mem_top
    simpa [I] using h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hMb : M ≠ ⊥ := by
    rintro rfl
    exact RingOfIntegers.not_isField (K := E) (Ring.isField_iff_maximal_bot.2 hM)
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hMb⟩
  have hxQ : x ∈ localization₂ Q.asIdeal N' := by
    rw [← h Q]
    exact (mem_localization_iff_exists_smul_mem Q x).2 ⟨1, (Ideal.ne_top_iff_one _).1 hM.ne_top, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff_exists_smul_mem Q x).1 hxQ
  exact hs (hIM (by simpa [I] using hsx))

theorem unimodular_ext : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N → IsUnimodular (hStd E n) N → Submodule.IsLattice E N' → IsUnimodular (hStd E n) N' → (∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' → localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') ∧ ((∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' ∨ localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') → N = N') := by
  intro E _ _ _ n N N' hl hu hl' hu'
  have part1 : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' →
      localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N' := by
    intro Q hQ
    ext x
    rw [mem_localization_conj_iff hl.fg hu Q x, mem_localization_conj_iff hl'.fg hu' Q x, hQ]
  refine ⟨part1, fun hor => ?_⟩
  have hall : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' := by
    intro Q
    rcases hor Q with h | h
    · exact h
    · have h' := part1 (conjPrime₂ Q) h
      rwa [conjP_involutive] at h'
  exact le_antisymm (le_of_forall_localized_eq hall) (le_of_forall_localized_eq fun Q => (hall Q).symm)

end GlobalTheory.GO.UniExt

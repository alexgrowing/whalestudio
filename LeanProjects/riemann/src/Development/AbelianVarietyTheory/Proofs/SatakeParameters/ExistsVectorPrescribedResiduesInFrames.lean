import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

namespace GlobalTheory.CRTFrame

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) (M : 𝓞 E) (hM : M ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P ((algebraMap (𝓞 E) E M)⁻¹ * algebraMap (𝓞 E) E z) := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {M} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hM
  have hex : ∃ m : ℕ, ¬ I ≤ P.asIdeal ^ m := by
    by_contra h
    push Not at h
    apply hI
    have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
    have := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal hP
    rw [eq_bot_iff, ← this]
    exact le_iInf h
  set m0 := Nat.find hex with hm0
  have hm0pos : m0 ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm0, h0, pow_zero] at this
    exact this (by rw [Ideal.one_eq_top]; exact le_top)
  refine ⟨m0 - 1, ?_⟩
  have hle : I ≤ P.asIdeal ^ (m0 - 1) := by
    have := Nat.find_min hex (show m0 - 1 < m0 by omega)
    push Not at this
    exact this
  have hnle : ¬ I ≤ P.asIdeal ^ (m0 - 1 + 1) := by
    rw [show m0 - 1 + 1 = m0 by omega]; exact Nat.find_spec hex
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hle
  have hQP : ¬ Q ≤ P.asIdeal := by
    intro h
    apply hnle
    rw [hQ, pow_succ]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.mp hQP
  intro z hz
  have hmem : z * s ∈ I := by
    rw [hQ]; exact Ideal.mul_mem_mul hz hsQ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hM' : algebraMap (𝓞 E) E M ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hM
  refine ⟨a, s, hsP, ?_⟩
  have h2 : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E M = algebraMap (𝓞 E) E z * algebraMap (𝓞 E) E s := by
    rw [← map_mul, ← map_mul, ha]
  field_simp
  linear_combination -h2

theorem approx_frames (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ) :
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  classical
  set w : SB → Sp E n := fun P => f P (y0 P) with hwdef
  set c : SB → Fin n → Fin n → E := fun P j l => (f P).symm (Pi.single j 1) l with hcdef
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    ((Finset.univ.image (fun x : SB × Fin n × Fin n => c x.1 x.2.1 x.2.2)) ∪
      (Finset.univ.image (fun x : SB × Fin n => w x.1 x.2)))
  set D : 𝓞 E := (b : 𝓞 E) with hDdef
  have hD : D ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hc : ∀ P j l, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * c P j l := by
    intro P j l
    obtain ⟨r, hr⟩ := hb (c P j l) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(P, j, l), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  have hw : ∀ P j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * w P j := by
    intro P j
    obtain ⟨r, hr⟩ := hb (w P j) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(P, j), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose cr hcr using hc
  choose wr hwr using hw
  have hN : ∀ P : SB, ((qOf P.1 : ℕ) : 𝓞 E) ≠ 0 := by
    intro P
    rw [Ne, Nat.cast_eq_zero]
    show Ideal.absNorm P.1.asIdeal ≠ 0
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  set M : SB → 𝓞 E := fun P => ((qOf P.1 : ℕ) : 𝓞 E) ^ (e P) * D * D with hMdef
  have hM : ∀ P, M P ≠ 0 := fun P => mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hN P)) hD) hD
  choose k hk using fun P : SB => exists_pow_intAt_div P.1 (M P) (hM P)
  set kk : HeightOneSpectrum (𝓞 E) → ℕ := fun P => if h : P ∈ SB then k ⟨P, h⟩ else 0 with hkkdef
  have crt : ∀ j : Fin n, ∃ z : 𝓞 E, ∀ (P : HeightOneSpectrum (𝓞 E)) (hP : P ∈ SB),
      z - wr ⟨P, hP⟩ j ∈ P.asIdeal ^ kk P := fun j =>
    IsDedekindDomain.exists_forall_sub_mem_ideal (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) kk
      (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun P => wr P j)
  choose z hz using crt
  have hD' : algebraMap (𝓞 E) E D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hD
  refine ⟨fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j), ?_⟩
  intro P l
  have hexp : ∀ v : Sp E n, (f P).symm v l = ∑ j, v j * c P j l := by
    intro v
    have hv : v = ∑ j, v j • (Pi.single j 1 : Sp E n) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, Finset.sum_apply, c]
  have hmem : (∑ j, (z j - wr P j) * cr P j l) ∈ P.1.asIdeal ^ k P := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    have := hz j P.1 P.2
    simpa [kk, P.2] using this
  have key := hk P _ hmem
  convert key using 1
  have h1 : (f P).symm (fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - y0 P
      = (f P).symm ((fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - w P) := by
    rw [map_sub]; simp [w]
  rw [h1, hexp, Finset.mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := hcr P j l
  have e2 := hwr P j
  simp only [M, map_mul, map_sub, map_pow, map_natCast, Pi.sub_apply]
  rw [e1, e2]
  have hq : ((qOf P.1 : ℕ) : E) ≠ 0 := by
    have := hN P
    intro h; apply this
    exact (IsFractionRing.injective (𝓞 E) E) (by rw [map_natCast, h, map_zero])
  field_simp

theorem approx_frames_target : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) :=
  fun E _ _ n SB f y0 e => approx_frames E n SB f y0 e

end GlobalTheory.CRTFrame

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.LevelHalf

theorem prime_of_between {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2) (J : Ideal (𝓞 K))
    (hle : Ideal.span {(p : 𝓞 K)} ≤ J) (h1 : J ≠ ⊤) (h2 : J ≠ Ideal.span {(p : 𝓞 K)}) :
    J.IsPrime ∧ J ≠ ⊥ := by
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 hle
  have hN' := congrArg Ideal.absNorm hC
  rw [map_mul, hN] at hN'
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN'.symm)
  have hi1 : i = 1 := by
    interval_cases i
    · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hieq; exact absurd hieq h1
    · rfl
    · exfalso
      rw [hieq] at hN'
      have hc : Ideal.absNorm C = 1 :=
        Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN'.symm.trans (mul_one _).symm)
      rw [Ideal.absNorm_eq_one_iff] at hc
      rw [hc, Ideal.mul_top] at hC
      exact h2 hC.symm
  rw [hi1, pow_one] at hieq
  refine ⟨Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible), ?_⟩
  intro h
  rw [h, Ideal.absNorm_bot] at hieq
  exact hp.ne_zero hieq.symm

theorem eq_sup_mul_sup {S : Type} [CommRing S] (I : Ideal S) (a b : S) (hab : IsCoprime a b)
    (h : a * b ∈ I) : I = (I ⊔ Ideal.span {a}) * (I ⊔ Ideal.span {b}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, v, huv⟩ := hab
    have e : x = (u * a) * x + x * (v * b) := by linear_combination (-x) * huv
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
        (Ideal.mem_sup_left hx))
      (Ideal.mul_mem_mul (Ideal.mem_sup_left hx)
        (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))))
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    refine sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ?_)
    rwa [Ideal.span_singleton_le_iff_mem]

theorem sup_ne {S : Type} [CommRing S] (σ : S →+* S) (I : Ideal S) (p : ℕ)
    (hp : Ideal.span {(p : S)} ≠ ⊤) (hm : I * I.map σ ≤ Ideal.span {(p : S)}) (hc : I ⊔ I.map σ = ⊤) :
    I ⊔ Ideal.span {(p : S)} ≠ ⊤ ∧ I ⊔ Ideal.span {(p : S)} ≠ Ideal.span {(p : S)} := by
  have hσ : (Ideal.span {(p : S)}).map σ = Ideal.span {(p : S)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  constructor
  · intro h
    have h' : I.map σ ⊔ Ideal.span {(p : S)} = ⊤ := by
      have := congrArg (Ideal.map σ) h
      rwa [Ideal.map_sup, hσ, Ideal.map_top] at this
    have h3 : IsCoprime (I * I.map σ) (Ideal.span {(p : S)}) :=
      IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.2 h) (Ideal.isCoprime_iff_sup_eq.2 h')
    rw [Ideal.isCoprime_iff_sup_eq, sup_eq_right.2 hm] at h3
    exact hp h3
  · intro h
    have hI : I ≤ Ideal.span {(p : S)} := sup_eq_right.1 h
    have hI' : I.map σ ≤ Ideal.span {(p : S)} := hσ ▸ Ideal.map_mono hI
    exact hp (top_le_iff.1 (hc ▸ sup_le hI hI'))

theorem half_eq_prod : ∀ (D : D7) (Q : Par D), Q.Pins → ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  intro D Q hQ
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hQ.2.1.1
  have hrt : (Q.H.rt : D.host.E) = D.host.sqrtMinusD := hQ.1.2.1
  have hw : Q.H.w0 = w0E D := by
    have h1 := Q.H.two_weight_eq_one_add_root
    have h2 := two_w0E D
    have h3 : Q.H.rt = rtE D := RingOfIntegers.ext hrt
    rw [h3, ← h2] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  set f := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) with hf
  set I := Q.l.Mb with hI
  have hIm : (I.comap f).map f = I := by
    apply le_antisymm Ideal.map_comap_le
    refine Q.l.fromK.le.trans ?_
    rw [Ideal.span_le]
    rintro a ⟨ha, ha'⟩
    have hr : a ∈ (f.toIntAlgHom).range := by
      refine (Algebra.adjoin_le ?_ : Algebra.adjoin ℤ {Q.H.w0} ≤ (f.toIntAlgHom).range) ha'
      rw [Set.singleton_subset_iff, hw]
      exact ⟨LPb.w0K D, LPb.algebraMap_w0K D⟩
    obtain ⟨y, hy⟩ := hr
    have hy' : f y = a := hy
    rw [← hy'] at ha ⊢
    exact Ideal.mem_map_of_mem f ha
  have hprod := Q.l.prod
  rw [hM, Nat.cast_mul] at hprod
  have hmap : ∀ p : ℕ, (I.comap f ⊔ Ideal.span {(p : 𝓞 D.host.K)}).map f = I ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
    intro p
    rw [Ideal.map_sup, hIm, Ideal.map_span, Set.image_singleton, map_natCast]
  have hspan : ∀ p : ℕ, (Ideal.span {(p : 𝓞 D.host.K)}).map f = Ideal.span {(p : 𝓞 D.host.E)} := by
    intro p
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have key : ∀ k : Fin 2, (I.comap f ⊔ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.K)}).IsPrime ∧
      (I.comap f ⊔ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.K)}) ≠ ⊥ := by
    intro k
    have hm : I * I.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
      rw [hI, hprod, Ideal.span_singleton_le_span_singleton]
      fin_cases k
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨h1, h2⟩ := sup_ne _ I _ (LPb.span_p_ne_top D (D.host.g_prime k)) hm Q.l.coprime
    refine prime_of_between (D.host.g_prime k) (LPb.absNorm_span_p D _) _ le_sup_right ?_ ?_
    · intro h
      apply h1
      rw [← hmap, h, Ideal.map_top]
    · intro h
      apply h2
      rw [← hmap, h, hspan]
  refine ⟨fun k => ⟨_, (key k).1, (key k).2⟩, fun k => Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), ?_⟩
  rw [Fin.prod_univ_two]
  show I = (I.comap f ⊔ _).map f * (I.comap f ⊔ _).map f
  rw [hmap, hmap]
  apply eq_sup_mul_sup
  · have := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using this.map (Int.castRingHom (𝓞 D.host.E))
  · rw [← Ideal.span_singleton_le_iff_mem, ← hprod]
    exact Ideal.mul_le_left

end GlobalTheory.LevelHalf

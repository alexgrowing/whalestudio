import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

variable {m : ℕ}

theorem algebraMap_locRing_eq_zero_of_mem (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ I) : algebraMap _ (locRing I t) a = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) a) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

theorem map_ptIdeal_eq_maximalIdeal (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hp : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hp, not_not]
    exact RingHom.mem_ker.mp ha
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hp b).mpr hb
    have hxn : ¬ IsUnit x := hx
    have ha : eval t a = 0 := by
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hp a).mpr hne
      rw [← hab] at hau
      exact hxn (isUnit_of_mul_isUnit_left hau)
    obtain ⟨u, hu⟩ := hbu
    have hx' : x = algebraMap _ (locRing I t) a * ↑u⁻¹ := by
      rw [← hab, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr ha))

theorem exists_den_of_mem_map (I D : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (hID : I ≤ D)
    (hp : ∀ h ∈ I, eval t h = 0) {f : MvPolynomial (Fin m) ℂ}
    (hf : algebraMap _ (locRing I t) f ∈ Ideal.map (algebraMap _ (locRing I t)) D) :
    ∃ s, eval t s ≠ 0 ∧ s * f ∈ D := by
  have key : ∀ x ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) D,
      ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧ x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∃ a ∈ D, ∃ b, eval t b ≠ 0 ∧
      x * algebraMap _ (locRing I t) b = algebraMap _ (locRing I t) a) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, ha, 1, by simp, by simp⟩
    · exact ⟨0, D.zero_mem, 1, by simp, by simp⟩
    · rintro x y _ _ ⟨a, ha, b, hb, hab⟩ ⟨c, hc, d, hd, hcd⟩
      refine ⟨a * d + c * b, D.add_mem (D.mul_mem_right _ ha) (D.mul_mem_right _ hc), b * d,
        by simpa using ⟨hb, hd⟩, ?_⟩
      simp only [map_add, map_mul, ← hab, ← hcd]
      ring
    · rintro c x _ ⟨a, ha, b, hb, hab⟩
      obtain ⟨u, v, hv, huv⟩ := exists_mk_locRing I t c
      refine ⟨u * a, D.mul_mem_left _ ha, v * b, by simpa using ⟨hv, hb⟩, ?_⟩
      simp only [smul_eq_mul, map_mul, ← hab, ← huv]
      ring
  obtain ⟨a, ha, b, hb, hab⟩ := key _ hf
  have h0 : algebraMap _ (locRing I t) (f * b - a) = 0 := by
    rw [map_sub, map_mul, hab, sub_self]
  obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
  refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
  have : s * b * f = s * (f * b - a) + s * a := by ring
  rw [this]
  exact D.add_mem (hID hsm) (D.mul_mem_left _ ha)

theorem radical_span_prod_eq {O ι : Type*} [CommRing O] [IsDomain O] (R : ι → O) (J : Finset ι)
    (hpr : ∀ i, Prime (R i)) (hna : ∀ i j, i ≠ j → ¬ Associated (R i) (R j)) :
    (Ideal.span {∏ i ∈ J, R i}).radical = Ideal.span {∏ i ∈ J, R i} := by
  classical
  apply le_antisymm _ Ideal.le_radical
  rintro g ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  have hdiv : ∀ i ∈ J, R i ∣ g := fun i hi =>
    (hpr i).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem R hi).trans hn)
  clear hn
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨c, rfl⟩ := ih fun i hi => hdiv i (Finset.mem_insert_of_mem hi)
    have hac := hdiv a (Finset.mem_insert_self _ _)
    rcases (hpr a).dvd_or_dvd hac with h | h
    · exfalso
      obtain ⟨j, hj, hd⟩ := (Prime.exists_mem_finset_dvd (hpr a) h)
      have hne : a ≠ j := fun e => ha (e ▸ hj)
      exact hna a j hne (((hpr a).dvd_prime_iff_associated (hpr j)).mp hd)
    · obtain ⟨d, rfl⟩ := h
      exact ⟨d, by ring⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

theorem exists_den_prod_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  classical
  intro m e I Dc t r Jf hID hp hreg hdim hspan hprime
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  set alg : MvPolynomial (Fin m) ℂ →+* locRing I t := algebraMap _ (locRing I t) with halg
  set R : Fin e → locRing I t := fun l => alg (r l) with hR
  have hspan' : Ideal.span (Set.range R) = IsLocalRing.maximalIdeal (locRing I t) := by
    rw [← map_ptIdeal_eq_maximalIdeal I t hp]
    exact hspan
  have hpr : ∀ i, Prime (R i) := prime_of_regular_params R hspan' hdim.symm
  have hna := (regular_params_spec R hspan' hdim.symm).2
  set Q : MvPolynomial (Fin m) ℂ := ∏ l ∈ Jf, r l with hQ
  have hPQ : alg Q = ∏ l ∈ Jf, R l := map_prod alg _ _

  have hpr2 : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (Ideal.map alg Dc ≤ 𝔓 ↔ alg Q ∈ 𝔓) := by
    intro 𝔓 h𝔓
    have hq1 : (Ideal.comap alg 𝔓).IsPrime := Ideal.comap_isPrime alg 𝔓
    have hq2 : I ≤ Ideal.comap alg 𝔓 := fun a ha => by
      rw [Ideal.mem_comap, halg, algebraMap_locRing_eq_zero_of_mem I t ha]
      exact 𝔓.zero_mem
    have hq3 : Ideal.comap alg 𝔓 ≤ ptIdeal t := fun a ha => by
      by_contra hne
      have hu := (isUnit_algebraMap_locRing_iff I t hp a).mpr fun h => hne (RingHom.mem_ker.mpr h)
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    rw [Ideal.map_le_iff_le_comap, hprime _ hq1 hq2 hq3, hPQ, Ideal.IsPrime.prod_mem_iff]
    rfl
  have hrad : (Ideal.map alg Dc).radical = Ideal.span {alg Q} := by
    rw [hPQ, ← radical_span_prod_eq R Jf hpr hna, ← hPQ, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
    congr 1
    ext 𝔓
    simp only [Set.mem_setOf_eq, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mpr h1, h2⟩⟩

  obtain ⟨h', hh', hQrad⟩ : ∃ h', eval t h' ≠ 0 ∧ h' * Q ∈ Dc.radical := by
    have h1 : alg Q ∈ (Ideal.map alg Dc).radical := by
      rw [hrad]; exact Ideal.mem_span_singleton_self _
    obtain ⟨N, hN⟩ := h1
    rw [← map_pow] at hN
    obtain ⟨s, hs, hsm⟩ := exists_den_of_mem_map I Dc t hID hp hN
    refine ⟨s, hs, N + 1, ?_⟩
    have : (s * Q) ^ (N + 1) = s ^ N * Q * (s * Q ^ N) := by ring
    rw [this]
    exact Dc.mul_mem_left _ hsm

  have hone : ∀ g ∈ Dc.radical, ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := by
    rintro g ⟨n, hn⟩
    have h1 : alg g ∈ (Ideal.map alg Dc).radical :=
      ⟨n, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hn⟩
    rw [hrad, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t c
    have h0 : algebraMap _ (locRing I t) (g * b - Q * a) = 0 := by
      change alg (g * b - Q * a) = 0
      have hab' : c * alg b = alg a := hab
      rw [map_sub, map_mul, map_mul, hc, ← hab']
      ring
    obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
    have : s * b * g = s * (g * b - Q * a) + Q * (s * a) := by ring
    rw [this, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right hsm)

  obtain ⟨S, hS⟩ : Dc.radical.FG := IsNoetherian.noetherian _
  have hSm : ∀ g, g ∈ S → ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := fun g hg =>
    hone g (hS ▸ Submodule.subset_span hg)
  choose! f hf0 hf1 using hSm
  set H : MvPolynomial (Fin m) ℂ := ∏ g ∈ S, f g with hH
  have hH0 : eval t H ≠ 0 := by
    rw [hH, map_prod]
    exact Finset.prod_ne_zero_iff.mpr hf0
  have hHS : Dc.radical ≤
      Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin m) ℂ) H) (Ideal.span {Q} ⊔ I) := by
    rw [← hS]
    refine Submodule.span_le.mpr fun g hg => ?_
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem f hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    rw [hH, hw, mul_comm (f g) w, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hf1 g hg)
  refine ⟨h' * H, by simpa using ⟨hh', hH0⟩, ?_, fun g hg => ?_⟩
  · have : h' * H * Q = H * (h' * Q) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hQrad
  · have h1 := hHS hg
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ h1

end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad

end

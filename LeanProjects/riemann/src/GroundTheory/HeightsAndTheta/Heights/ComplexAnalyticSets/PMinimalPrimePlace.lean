import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMinimalPrimePlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocalOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

namespace MinimalPrimePlace

variable {A B : Type*} [CommRing A] [CommRing B]

theorem eq_zero_of_forall_mem_minimalPrimes [IsReduced A] {x : A} (h : ∀ q ∈ minimalPrimes A, x ∈ q) :
    x = 0 := by
  have hx : x ∈ sInf (minimalPrimes A) := Submodule.mem_sInf.2 h
  have hrad : sInf (minimalPrimes A) = (⊥ : Ideal A).radical := Ideal.sInf_minimalPrimes
  rw [hrad] at hx
  obtain ⟨k, hk⟩ := hx
  exact IsNilpotent.eq_zero ⟨k, Ideal.mem_bot.1 hk⟩

theorem mem_nonZeroDivisors_of_notMem_minimalPrimes [IsReduced A] {w : A}
    (hw : ∀ q ∈ minimalPrimes A, w ∉ q) : w ∈ nonZeroDivisors A := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩ <;>
    refine eq_zero_of_forall_mem_minimalPrimes fun q hq ↦ ?_
  · exact (hq.1.1.mem_or_mem (hy ▸ q.zero_mem : w * y ∈ q)).resolve_left (hw q hq)
  · exact (hq.1.1.mem_or_mem (hy ▸ q.zero_mem : y * w ∈ q)).resolve_right (hw q hq)

theorem eq_of_le_of_mem_minimalPrimes {q q' : Ideal A} (hq : q ∈ minimalPrimes A) (hq' : q' ∈ minimalPrimes A)
    (h : q ≤ q') : q = q' :=
  le_antisymm h (hq'.2 hq.1 h)

theorem exists_separating [IsNoetherianRing A] {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    ∃ s t : A, t ∈ p ∧ s ∉ p ∧ ∀ q ∈ minimalPrimes A, q ≠ p → s ∈ q ∧ t ∉ q := by
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hpP : p.IsPrime := hp.1.1
  have hF : ¬ (hfin.toFinset.erase p).inf id ≤ p := by
    rw [hpP.inf_le']
    rintro ⟨q, hq, hqp⟩
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hq
    exact hq.1 (eq_of_le_of_mem_minimalPrimes hq.2 hp hqp)
  obtain ⟨s, hsF, hsp⟩ := SetLike.not_le_iff_exists.1 hF
  have hsq : ∀ q ∈ minimalPrimes A, q ≠ p → s ∈ q := fun q hq hqp ↦
    Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hqp, hfin.mem_toFinset.2 hq⟩) hsF
  have hU : ¬ ((p : Set A) ⊆ ⋃ q ∈ minimalPrimes A \ {p}, ((fun q : Ideal A ↦ q) q : Set A)) := by
    rw [Ideal.subset_union_prime_finite (hfin.subset Set.sdiff_subset) p p (fun q hq _ _ ↦ hq.1.1.1)]
    rintro ⟨q, hq, hpq⟩
    exact hq.2 (eq_of_le_of_mem_minimalPrimes hp hq.1 hpq).symm
  obtain ⟨t, htp, htU⟩ := Set.not_subset.1 hU
  refine ⟨s, t, htp, hsp, fun q hq hqp ↦ ⟨hsq q hq hqp, fun htq ↦ htU ?_⟩⟩
  exact Set.mem_biUnion (⟨hq, hqp⟩ : q ∈ minimalPrimes A \ {p}) htq

theorem le_comap_nonZeroDivisors [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) :
    nonZeroDivisors A ≤ (nonZeroDivisors B).comap π := fun _u hu ↦
  mem_nonZeroDivisors_of_ne_zero fun h ↦
    Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hker) (RingHom.mem_ker.2 h) hu

abbrev fracMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) :
    FractionRing A →+* FractionRing B :=
  IsLocalization.map (S := FractionRing A) (FractionRing B) π (le_comap_nonZeroDivisors π hker)

theorem fracMap_aeval [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (x : FractionRing A)
    (G : Polynomial A) :
    fracMap π hker (Polynomial.aeval x G) = Polynomial.aeval (fracMap π hker x) (G.map π) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂,
    IsLocalization.map_comp]

theorem isIntegral_fracMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) {x : FractionRing A}
    (hx : IsIntegral A x) : IsIntegral B (fracMap π hker x) := by
  obtain ⟨G, hG, hGx⟩ := hx
  refine ⟨G.map π, hG.map π, ?_⟩
  have h := fracMap_aeval π hker x G
  rw [Polynomial.aeval_def, Polynomial.aeval_def, hGx, map_zero] at h
  exact h.symm

theorem exists_fracMap_unit [IsNoetherianRing A] [IsReduced A] [IsDomain B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π ∈ minimalPrimes A) :
    ∃ e : FractionRing A, fracMap π hker e = 1 ∧ (∀ z, fracMap π hker z = 0 → e * z = 0) ∧
      ∀ y : FractionRing B, ∃ x, fracMap π hker x = y := by
  obtain ⟨s, t, htp, hsp, hq⟩ := exists_separating hker
  have hpP : (RingHom.ker π).IsPrime := hker.1.1
  have hπt : π t = 0 := RingHom.mem_ker.1 htp
  have hπs : π s ≠ 0 := fun h ↦ hsp (RingHom.mem_ker.2 h)
  have hst : ∀ c, c ∉ RingHom.ker π → c * s + t ∈ nonZeroDivisors A := by
    intro c hc
    refine mem_nonZeroDivisors_of_notMem_minimalPrimes fun q hqm hmem ↦ ?_
    by_cases hqp : q = RingHom.ker π
    · rw [hqp] at hmem
      have hcs : c * s ∈ RingHom.ker π := by simpa using (RingHom.ker π).sub_mem hmem htp
      rcases hpP.mem_or_mem hcs with h | h
      · exact hc h
      · exact hsp h
    · obtain ⟨hs, ht⟩ := hq q hqm hqp
      exact ht (by simpa using q.sub_mem hmem (q.mul_mem_left c hs))
  have h1 : (1 : A) ∉ RingHom.ker π := fun h ↦ hpP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hw : s + t ∈ nonZeroDivisors A := by simpa using hst 1 h1
  have hsa : ∀ a ∈ RingHom.ker π, s * a = 0 := fun a ha ↦ eq_zero_of_forall_mem_minimalPrimes fun q hqm ↦ by
    by_cases hqp : q = RingHom.ker π
    · rw [hqp]; exact Ideal.mul_mem_left _ _ ha
    · exact Ideal.mul_mem_right _ _ (hq q hqm hqp).1
  have hinj := IsFractionRing.injective B (FractionRing B)
  refine ⟨IsLocalization.mk' (FractionRing A) s (⟨s + t, hw⟩ : nonZeroDivisors A), ?_, ?_, ?_⟩
  · have h := congrArg (fracMap π hker)
      (IsLocalization.mk'_spec (FractionRing A) s (⟨s + t, hw⟩ : nonZeroDivisors A))
    rw [map_mul, IsLocalization.map_eq, IsLocalization.map_eq] at h
    simp only [map_add, hπt, add_zero] at h
    have hne : algebraMap B (FractionRing B) (π s) ≠ 0 := fun h0 ↦ hπs (hinj (by rw [h0, map_zero]))
    exact mul_right_cancel₀ hne (h.trans (one_mul _).symm)
  · intro z hz
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
    have h := congrArg (fracMap π hker) (IsLocalization.mk'_spec (FractionRing A) a u)
    rw [map_mul, hz, zero_mul, IsLocalization.map_eq] at h
    have ha : a ∈ RingHom.ker π := RingHom.mem_ker.2 (hinj (by rw [← h, map_zero]))
    have hu : IsUnit (algebraMap A (FractionRing A) ((s + t) * u)) :=
      IsLocalization.map_units (FractionRing A) (⟨(s + t) * u, Submonoid.mul_mem _ hw u.2⟩ : nonZeroDivisors A)
    refine (hu.mul_left_eq_zero).1 ?_
    rw [map_mul, mul_mul_mul_comm, IsLocalization.mk'_spec, IsLocalization.mk'_spec, ← map_mul, hsa a ha,
      map_zero]
  · intro y
    obtain ⟨⟨b, v⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
    obtain ⟨a, rfl⟩ := hπ b
    obtain ⟨c, hc⟩ := hπ v
    have hcp : c ∉ RingHom.ker π := fun h ↦ nonZeroDivisors.ne_zero v.2 (by rw [← hc]; exact RingHom.mem_ker.1 h)
    refine ⟨IsLocalization.mk' (FractionRing A) (a * s) (⟨c * s + t, hst c hcp⟩ : nonZeroDivisors A), ?_⟩
    rw [IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul, map_add, hπt, add_zero, hc]
    ring

theorem isIntegral_mul_of_fracMap [IsDomain B] (π : A →+* B) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ∈ minimalPrimes A) {e x : FractionRing A} (he1 : fracMap π hker e = 1)
    (hek : ∀ z, fracMap π hker z = 0 → e * z = 0) (hx : IsIntegral B (fracMap π hker x)) :
    IsIntegral A (e * x) := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨G, hGmap, -, hG⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hπ g) hg
  refine ⟨Polynomial.X * G, Polynomial.monic_X.mul hG, ?_⟩
  have hz : e * Polynomial.aeval (e * x) G = 0 := by
    refine hek _ ?_
    rw [fracMap_aeval, hGmap, map_mul, he1, one_mul, Polynomial.aeval_def]
    exact hgx
  rw [Polynomial.aeval_def] at hz
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
  linear_combination x * hz

def normMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) :
    integralClosure A (FractionRing A) →+* integralClosure B (FractionRing B) :=
  ((fracMap π hker).comp (integralClosure A (FractionRing A)).val.toRingHom).codRestrict
    (integralClosure B (FractionRing B)) fun x ↦ isIntegral_fracMap π hker x.2

theorem normMap_algebraMap [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A) :
    normMap π hker (algebraMap A (integralClosure A (FractionRing A)) a) =
      algebraMap B (integralClosure B (FractionRing B)) (π a) :=
  Subtype.ext (IsLocalization.map_eq (S := FractionRing A) (Q := FractionRing B) (g := π)
    (hy := le_comap_nonZeroDivisors π hker) (x := a))

theorem exists_localization_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (ε : R) (hε1 : φ ε = 1) (hε : ∀ z, φ z = 0 → ε * z = 0) (P' : Ideal S)
    [P'.IsPrime] :
    ∃ E : Localization.AtPrime (P'.comap φ) ≃+* Localization.AtPrime P',
      ∀ r, E (algebraMap R _ r) = algebraMap S _ (φ r) := by
  let _ : Algebra R (Localization.AtPrime P') := ((algebraMap S (Localization.AtPrime P')).comp φ).toAlgebra
  have halg : ∀ r, algebraMap R (Localization.AtPrime P') r = algebraMap S _ (φ r) := fun _ ↦ rfl
  have : IsLocalization (P'.comap φ).primeCompl (Localization.AtPrime P') := by
    rw [isLocalization_iff]
    refine ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
    · rw [halg]
      exact IsLocalization.map_units (Localization.AtPrime P') (⟨φ y, y.2⟩ : P'.primeCompl)
    · obtain ⟨⟨b, v⟩, rfl⟩ := IsLocalization.mk'_surjective P'.primeCompl z
      obtain ⟨a, rfl⟩ := hφ b
      obtain ⟨c, hc⟩ := hφ (v : S)
      have hcP : c ∈ (P'.comap φ).primeCompl := by
        show φ c ∉ P'
        rw [hc]
        exact v.2
      refine ⟨(a, ⟨c, hcP⟩), ?_⟩
      simp only [halg, hc]
      exact IsLocalization.mk'_spec _ _ _
    · rw [halg, halg] at h
      obtain ⟨c', hc'⟩ := (IsLocalization.eq_iff_exists P'.primeCompl _).1 h
      obtain ⟨c0, hc0⟩ := hφ (c' : S)
      have hcP : ε * c0 ∈ (P'.comap φ).primeCompl := by
        show φ (ε * c0) ∉ P'
        rw [map_mul, hε1, one_mul, hc0]
        exact c'.2
      refine ⟨⟨ε * c0, hcP⟩, ?_⟩
      have hz := hε (c0 * (x - y)) (by rw [map_mul, map_sub, hc0, mul_sub, hc', sub_self])
      show ε * c0 * x = ε * c0 * y
      linear_combination hz
  exact ⟨(IsLocalization.algEquiv (P'.comap φ).primeCompl (Localization.AtPrime (P'.comap φ))
    (Localization.AtPrime P')).toRingEquiv, fun r ↦ AlgEquiv.commutes _ r⟩

theorem exists_maximal_ord_eq [IsNoetherianRing A] [IsReduced A] [IsDomain B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π ∈ minimalPrimes A)
    (P' : MaximalSpectrum (integralClosure B (FractionRing B))) :
    ∃ P : MaximalSpectrum (integralClosure A (FractionRing A)), ∀ a : A,
      Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap A (integralClosure A (FractionRing A)) a)) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap _ (Localization.AtPrime P'.asIdeal) (algebraMap B (integralClosure B (FractionRing B)) (π a))) := by
  obtain ⟨e, he1, hek, hsurj⟩ := exists_fracMap_unit π hπ hker
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap π hπ hker (x := 1) he1 hek (by rw [map_one]; exact isIntegral_one)
  have hφ : Function.Surjective (normMap π hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral A (e * x) :=
      isIntegral_mul_of_fracMap π hπ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨e * x, hint⟩, Subtype.ext ?_⟩
    show fracMap π hker (e * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap π hker ⟨e, he⟩ = 1 := Subtype.ext he1
  have hε : ∀ z, normMap π hker z = 0 → ⟨e, he⟩ * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have := P'.isMaximal
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap π hker) hφ ⟨e, he⟩ hε1 hε P'.asIdeal
  refine ⟨⟨P'.asIdeal.comap (normMap π hker), Ideal.comap_isMaximal_of_surjective _ hφ⟩, fun a ↦ ?_⟩
  rw [← ord_ringEquiv E, hE, normMap_algebraMap]

end MinimalPrimePlace

open MinimalPrimePlace in

theorem MinimalPrimePlace.proof : MinimalPrimePlace.Statement := by
  intro n I J q hI hJ hJq P'
  have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
      J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
    Ideal.map_mono hJ.1.2
  let π : curveLocalRing I q →+* curveLocalRing J q := Ideal.Quotient.factor hle
  have hπalg : ∀ f, π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) =
      algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f := fun f ↦ Ideal.Quotient.factor_mk hle _
  have hJd : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J :=
    Set.disjoint_left.2 fun x hx hxJ ↦ hx (hJq hxJ)
  have hJP : (J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ J hJ.1.1 hJd
  have hJc : (J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))).comap
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = J :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ hJ.1.1 hJd
  have _ : IsDomain (curveLocalRing J q) := Ideal.Quotient.isDomain _
  have _ : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hI
  have hkerJ : ∀ f, algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f = 0 ↔ f ∈ J := by
    intro f
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q))))) (a := algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q))) f)).trans (by rw [← Ideal.mem_comap, hJc])
  have hker : RingHom.ker π ∈ minimalPrimes (curveLocalRing I q) := by
    refine ⟨⟨RingHom.ker_isPrime π, bot_le⟩, fun Q hQ hQle ↦ ?_⟩
    have _ : Q.IsPrime := hQ.1
    have hIQ : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) := fun f hf ↦ by
      have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hf)
      show _ ∈ Q
      rw [h0]
      exact Q.zero_mem
    have hQJ : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) ≤ J := fun f hf ↦
      (hkerJ f).1 (by rw [← hπalg]; exact RingHom.mem_ker.1 (hQle hf))
    have hJQ := hJ.2 ⟨Ideal.comap_isPrime _ Q, hIQ⟩ hQJ
    intro z hz
    obtain ⟨f, s, hs, hfs⟩ := curveLocalRing_eq_div I q z
    have hf : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ Q :=
      hJQ ((hkerJ f).1 (by rw [← hπalg, ← hfs, map_mul, RingHom.mem_ker.1 hz, zero_mul]))
    rw [← hfs] at hf
    exact (Ideal.mul_unit_mem_iff_mem Q hs).1 hf
  obtain ⟨P, hP⟩ := exists_maximal_ord_eq π (Ideal.Quotient.factor_surjective hle) hker P'
  refine ⟨P, fun f ↦ ?_⟩
  have h := hP (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hπalg] at h
  exact h

end

end GroundTheory.Heights₂.Heights

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.OneNotMemOfIsPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

namespace regularityLocalFlat_holds

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]

def coneVarMap (hPW : P ≤ W) (v : ∀ k, ι k) : MvPolynomial K (locRing P W) →ₐ[locRing P W] coneLocRing P W hPW :=
  aeval fun k => algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩))

def varMono (v : ∀ k, ι k) (e : K →₀ ℕ) : MRing ι :=
  ∏ k, (X ⟨k, v k⟩ : MRing ι) ^ e k

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem coe_algebraMap_cone (hPW : P ≤ W) (a : MRing ι ⧸ P) :
    ((algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) a : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) a :=
  rfl

variable {P W} in
theorem homog_varMono (v : ∀ k, ι k) (e : K →₀ ℕ) : IsMultiHomog (varMono v e : MRing ι) ⇑e := by
  classical
  have h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, v k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • (Pi.single k 1 : K → ℕ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X k (v k)) (e k)) ih
  have e' : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = ⇑e := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := h Finset.univ
  rwa [e'] at this

omit [∀ k, Fintype (ι k)] in
theorem varMono_notMem {I : Ideal (MRing ι)} [I.IsPrime] {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ I) (e : K →₀ ℕ) : varMono v e ∉ I := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

theorem coneVarMap_coe (hPW : P ≤ W) (v : ∀ k, ι k) (G : MvPolynomial K (locRing P W)) :
    ((coneVarMap P W hPW v G : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) =
      ∑ e ∈ G.support, ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P (varMono v e) := by
  rw [coneVarMap, aeval_def, eval₂_eq']
  change (coneLocRing P W hPW).val _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_prod, varMono, map_prod]
  simp only [map_pow]
  rfl

variable {P W} in

theorem exists_clear (hPW : P ≤ W) (G : MvPolynomial K (locRing P W)) :
    ∃ (V : MRing ι) (b : K → ℕ) (N : (K →₀ ℕ) → MRing ι), IsMultiHomog V b ∧ V ∉ W ∧
      ∀ e, IsMultiHomog (N e) b ∧
        ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P V = fracHom P (N e) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial e c =>
    obtain ⟨u, w, a, hu, hw, hwW, hc⟩ := (mem_locRing_iff hPW).mp c.2
    refine ⟨w, a, fun e' => if e = e' then u else 0, hw, hwW, fun e' => ⟨?_, ?_⟩⟩
    · dsimp only
      split_ifs
      · exact hu
      · exact homog_zero a
    · rw [coeff_monomial]
      dsimp only
      split_ifs
      · exact hc
      · simp
  | add G1 G2 h1 h2 =>
    obtain ⟨V1, b1, N1, hV1, hV1W, hN1⟩ := h1
    obtain ⟨V2, b2, N2, hV2, hV2W, hN2⟩ := h2
    refine ⟨V1 * V2, b1 + b2, fun e => N1 e * V2 + N2 e * V1, homog_mul hV1 hV2,
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hV1W hV2W, fun e => ⟨?_, ?_⟩⟩
    · refine homog_add (homog_mul (hN1 e).1 hV2) ?_
      rw [add_comm b1 b2]
      exact homog_mul (hN2 e).1 hV1
    · rw [coeff_add]
      change (((coeff e G1 : locRing P W) : FractionRing (MRing ι ⧸ P)) + (coeff e G2 : locRing P W)) * _ = _
      simp only [map_add, map_mul]
      rw [← (hN1 e).2, ← (hN2 e).2]
      ring

variable {P W} in

theorem coneVarMap_mul_clear (hPW : P ≤ W) (v : ∀ k, ι k) (G : MvPolynomial K (locRing P W))
    {V : MRing ι} {b : K → ℕ} {N : (K →₀ ℕ) → MRing ι}
    (hN : ∀ e, IsMultiHomog (N e) b ∧
        ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P V = fracHom P (N e)) :
    ((coneVarMap P W hPW v G : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) * fracHom P V =
      fracHom P (∑ e ∈ G.support, N e * varMono v e) := by
  rw [coneVarMap_coe, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, ← (hN e).2]
  ring

theorem mem_of_clear_mem {I : Ideal (MRing ι)} [I.IsPrime] (hI : IsMultiHomogIdeal I) {v : ∀ k, ι k}
    (hvI : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ I) (s : Finset (K →₀ ℕ)) {b : K → ℕ} {N : (K →₀ ℕ) → MRing ι}
    (hN : ∀ e, IsMultiHomog (N e) b) (h : ∑ e ∈ s, N e * varMono v e ∈ I) : ∀ e ∈ s, N e ∈ I := by
  intro e he
  have := mem_of_sum_mem hI s (fun e => N e * varMono v e) (fun e => b + ⇑e) ?_
    (fun e _ => homog_mul (hN e) (homog_varMono v e)) h e he
  · exact (Ideal.IsPrime.mem_or_mem ‹_› this).resolve_right (varMono_notMem hvI e)
  · intro e1 _ e2 _ h12
    exact DFunLike.coe_injective (add_left_cancel h12)

variable {P W} in

theorem coneVarMap_injective (hPW : P ≤ W) (hPh : IsMultiHomogIdeal P) {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) : Function.Injective (coneVarMap P W hPW v) := by
  rw [injective_iff_map_eq_zero]
  intro G hG
  obtain ⟨V, b, N, -, hVW, hN⟩ := exists_clear hPW G
  have hV0 : fracHom P V ≠ 0 := by
    rw [Ne, fracHom_eq_zero_iff]
    exact fun h => hVW (hPW h)
  have hsum := coneVarMap_mul_clear hPW v G hN
  rw [hG] at hsum
  have hNum : ∑ e ∈ G.support, N e * varMono v e ∈ P := by
    rw [← fracHom_eq_zero_iff, ← hsum]
    simp
  have hvP : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ P := fun k h => hv k (hPW h)
  have hNP : ∀ e ∈ G.support, N e ∈ P := mem_of_clear_mem hPh hvP G.support (fun e => (hN e).1) hNum
  refine MvPolynomial.ext _ _ fun e => ?_
  rw [coeff_zero]
  by_contra hne
  have he : e ∈ G.support := mem_support_iff.mpr hne
  have h1 := (hN e).2
  rw [fracHom_eq_zero_iff.mpr (hNP e he)] at h1
  have h2 : ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) = 0 :=
    (mul_eq_zero.mp h1).resolve_right hV0
  exact hne (Subtype.ext h2)

variable {P W} in

theorem isUnit_algebraMap_cone (hPW : P ≤ W) {g : MRing ι} (hg : g ∉ W) :
    IsUnit (algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P g)) :=
  IsLocalization.map_units (coneLocRing P W hPW)
    (⟨_, ⟨g, hg, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))

variable {P W} in

theorem isUnit_coneVarMap (hPW : P ≤ W) (hWh : IsMultiHomogIdeal W) {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) (G : MvPolynomial K (locRing P W)) {e : K →₀ ℕ}
    (he : IsUnit (coeff e G)) : IsUnit (coneVarMap P W hPW v G) := by
  obtain ⟨V, b, N, hV, hVW, hN⟩ := exists_clear hPW G
  have hNe : N e ∉ W := (isUnit_iff hPW (coeff e G) (hN e).1 hV hVW (hN e).2).mp he
  have hesupp : e ∈ G.support := mem_support_iff.mpr he.ne_zero
  have hNum : ∑ e ∈ G.support, N e * varMono v e ∉ W := fun h =>
    hNe (mem_of_clear_mem hWh hv G.support (fun e => (hN e).1) h e hesupp)
  have heq : coneVarMap P W hPW v G *
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P V) =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW)
        (Ideal.Quotient.mk P (∑ e ∈ G.support, N e * varMono v e)) :=
    Subtype.ext (coneVarMap_mul_clear hPW v G hN)
  exact isUnit_of_mul_isUnit_left (heq ▸ isUnit_algebraMap_cone hPW hNum)

variable {P W} in

theorem exists_lift (hPW : P ≤ W) {v : ∀ k, ι k} (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) (f : MRing ι) :
    ∃ F, coneVarMap P W hPW v F =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c =>
    refine ⟨(c : MvPolynomial K (locRing P W)), ?_⟩
    rw [map_intCast, eq_intCast (MvPolynomial.C) c, map_intCast, map_intCast]
  | add p q hp hq =>
    obtain ⟨F, hF⟩ := hp
    obtain ⟨G, hG⟩ := hq
    exact ⟨F + G, by rw [map_add, hF, hG, map_add, map_add]⟩
  | mul_X p n hp =>
    obtain ⟨F, hF⟩ := hp
    obtain ⟨k, i⟩ := n
    have hX0 : fracHom P (X ⟨k, v k⟩) ≠ 0 := by
      rw [Ne, fracHom_eq_zero_iff]
      exact fun h => hv k (hPW h)
    have hr : fracHom P (X ⟨k, i⟩) / fracHom P (X ⟨k, v k⟩) ∈ locRing P W :=
      div_mem_locRing hPW (homog_X k i) (homog_X k (v k)) (hv k)
    refine ⟨F * (MvPolynomial.C (⟨_, hr⟩ : locRing P W) * X k), ?_⟩
    have hX : coneVarMap P W hPW v (X k) =
        algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩)) :=
      aeval_X _ _
    rw [map_mul, map_mul, hF, algHom_C, hX]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, coe_algebraMap_cone, coe_algebraMap_cone, coe_algebraMap_cone,
      locRing.algebraMap_cone_coe, ← fracHom_apply, ← fracHom_apply, ← fracHom_apply, map_mul]
    rw [div_mul_cancel₀ _ hX0]

variable {P W} in

theorem exists_isUnit_coeff (hPW : P ≤ W) {v : ∀ k, ι k} (G : MvPolynomial K (locRing P W))
    {g : MRing ι} (hg : g ∉ W)
    (hG : coneVarMap P W hPW v G =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P g)) :
    ∃ e, IsUnit (coeff e G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨V, b, N, hV, hVW, hN⟩ := exists_clear hPW G
  have hNW : ∀ e, N e ∈ W := fun e => by
    by_contra h
    exact hcon e ((isUnit_iff hPW _ (hN e).1 hV hVW (hN e).2).mpr h)
  have hsum := coneVarMap_mul_clear hPW v G hN
  rw [hG] at hsum
  have h1 : fracHom P (∑ e ∈ G.support, N e * varMono v e - g * V) = 0 := by
    rw [map_sub, ← hsum, map_mul]
    exact sub_self _
  rw [fracHom_eq_zero_iff] at h1
  have h2 : g * V ∈ W := by
    have := W.sub_mem (W.sum_mem (t := G.support) fun e _ => W.mul_mem_right (varMono v e) (hNW e)) (hPW h1)
    simpa using this
  exact (Ideal.IsPrime.mem_or_mem ‹_› h2).elim hg hVW

theorem isPrime_map_C {A : Type*} [CommRing A] (σ : Type*) (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

variable {P W} in

theorem isLocalization_coneVarMap (hPW : P ≤ W) (hPh : IsMultiHomogIdeal P) (hWh : IsMultiHomogIdeal W)
    (v : ∀ k, ι k) (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) :
    haveI := isLocalRing hPW
    letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
    haveI := isPrime_map_C K (maximalIdeal (locRing P W))
    IsLocalization ((maximalIdeal (locRing P W)).map
      (C : locRing P W →+* MvPolynomial K (locRing P W))).primeCompl (coneLocRing P W hPW) := by
  have := isLocalRing hPW
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C K (maximalIdeal (locRing P W))
  rw [isLocalization_iff]
  refine ⟨fun G => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨G, hG⟩ := G
    have : ∃ e, IsUnit (coeff e G) := by
      by_contra h
      push Not at h
      exact hG (mem_map_C_iff.mpr fun e => (IsLocalRing.mem_maximalIdeal _).mpr (h e))
    obtain ⟨e, he⟩ := this
    exact isUnit_coneVarMap hPW hWh hv G he
  · obtain ⟨⟨x, s⟩, hz⟩ := IsLocalization.surj (W.primeCompl.map (Ideal.Quotient.mk P)) z
    obtain ⟨g, hg, hgs⟩ := s.2
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨F, hF⟩ := exists_lift hPW hv f
    obtain ⟨G, hG⟩ := exists_lift hPW hv g
    have hGq : G ∈ ((maximalIdeal (locRing P W)).map C).primeCompl := by
      intro hmem
      obtain ⟨e, he⟩ := exists_isUnit_coeff hPW G hg hG
      exact (IsLocalRing.mem_maximalIdeal _).mp (mem_map_C_iff.mp hmem e) he
    refine ⟨⟨F, ⟨G, hGq⟩⟩, ?_⟩
    change z * coneVarMap P W hPW v G = coneVarMap P W hPW v F
    rw [hF, hG, hgs]
    exact hz
  · exact ⟨1, by rw [coneVarMap_injective hPW hPh hv hxy]⟩

end regularityLocalFlat_holds

end

end GroundTheory.Heights₂.Heights.Inter

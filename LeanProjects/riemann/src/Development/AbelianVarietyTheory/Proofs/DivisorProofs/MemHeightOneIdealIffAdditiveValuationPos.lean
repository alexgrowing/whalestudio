import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeLoss

open IsDedekindDomain

theorem additiveValuation_mul_of_ne_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem additiveValuation_conj_place_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneIdeal_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conj (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneIdeal_iff_additiveValuation_pos _ y hy, mem_heightOneIdeal_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conj_place_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

theorem logWeight_conj (D : D7) (w : D.what₂.places.Pl) :
    SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w := by
  unfold SizeData₂.lwP
  rw [plEq_conj]
  exact Formalism.DivisionValues.ValuationRepresentative.lw_conjPl (D.plEq w)

theorem additiveValuation_residueChar_eq_ramIndex (D : D7) (w : D.what₂.places.Pl) :
    vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have h0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.val_eq w _ h0
  rw [D.what₂.places.val_resChar] at h1
  exact_mod_cast h1.symm

theorem exists_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset D.what₂.places.Pl, ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p := by
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨(T.map D.plEq.symm.toEmbedding).filter (fun w => D.what₂.places.resChar w = p), fun w => ?_⟩
  rw [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm, hT]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ resChar_mem D w, h⟩⟩

theorem sum_half (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p) (y : D.what₂.LL) (hy : y * star y = (p : D.what₂.LL)) :
    ∑ w ∈ S, 2 * SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) = Real.log p := by
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  have hconj : ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) =
      ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) := by
    refine Finset.sum_nbij' D.what₂.places.conj D.what₂.places.conj ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      rw [logWeight_conj, additiveValuation_conj_place_eq_star]
  have hm := factEtaMean D p hp S hS
  rw [← hm]
  have : ∀ w ∈ S, lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ) =
      SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) + SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) := by
    intro w hw
    have h1 := additiveValuation_residueChar_eq_ramIndex D w
    rw [(hS w).1 hw, ← hy, additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)] at h1
    have h2 : (D.what₂.places.ramIdx w : ℝ) = (vAdd (D.plEq w) y : ℝ) + (vAdd (D.plEq w) (star y) : ℝ) := by
      exact_mod_cast h1.symm
    rw [h2, ← mul_add]
    rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hconj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem conj_sigmaOf {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) :
    H.conj (H.sigmaOf g x) = H.sigmaOf g (H.conj x) := by
  have h1 : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj :=
    map_mul (H.gal).symm g (R.cc)
  have h2 : H.sigmaOf (R.cc * g) = H.conj * H.sigmaOf g :=
    map_mul (H.gal).symm (R.cc) g
  have h3 : H.conj * H.sigmaOf g = H.sigmaOf g * H.conj := by rw [← h1, ← h2, mul_comm]
  exact congrArg (fun s : H.E ≃ₐ[ℚ] H.E => s x) h3

theorem tauPib_norm {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    tauPib X i τ * star (tauPib X i τ) = (D.host.g i : D.what₂.LL) := by
  unfold tauPib tauLL
  rw [← D.embE_conj, conj_sigmaOf, ← map_mul, ← map_mul, ← map_mul, X.piG_norm]
  simp

theorem host_g_ne_mem_A_T {D : D7} (X : ErrX D) (u : D.what₂.Word) (i : Fin 2) : D.host.g i ≠ (D.mem u).A.T := by
  intro h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + (D.host.g i : 𝓞 D.host.E) * b := by
    have hd : D.host.g i ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
      refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨k, hk⟩ := hd
    refine ⟨k * a, ?_⟩
    rw [hk] at ha
    push_cast at ha
    linear_combination ha
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  rw [← h, hb] at hn
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    (IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe)
  set b' : 𝓞 D.host.E := ⟨_, hbi⟩ with hb'
  have hu : (D.host.g i : 𝓞 D.host.E) * (1 - b - b' - D.host.g i * b * b') = 1 := by
    apply Subtype.ext
    have e : ((b' : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E) := rfl
    simp only [map_add, map_mul, map_one, map_natCast] at hn
    change algebraMap _ D.host.E ((D.host.g i : 𝓞 D.host.E) * (1 - b - b' - D.host.g i * b * b')) = algebraMap _ D.host.E (1 : 𝓞 D.host.E)
    simp only [map_sub, map_mul, map_one, map_natCast]
    change _ * (1 - (b : D.host.E) - (b' : D.host.E) - _ * (b : D.host.E) * (b' : D.host.E)) = 1
    rw [e]
    linear_combination -hn
  have hunit : IsUnit ((D.host.g i : ℤ)) := by
    have : IsUnit (algebraMap ℤ (𝓞 D.host.E) (D.host.g i : ℤ)) := by
      simpa using IsUnit.of_mul_eq_one _ hu
    exact isUnit_of_map_unit (algebraMap ℤ (𝓞 D.host.E)) _ this
  have := Int.isUnit_iff.1 hunit
  have h2 := (D.host.g_prime i).two_le
  omega

theorem sum_over_g {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (hE : L.EDef X K c)
    (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (i : Fin 2) :
    ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w) =
      ((∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ)) * Real.log (D.host.g i) +
      2 * ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) +
      2 * (c.g * (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)) * Real.log (D.host.g i) := by
  obtain ⟨S, hS⟩ := exists_over D _ (D.host.g_prime i)
  have h1 : ∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w) =
      ∑ w ∈ S, SizeData₂.sz w (L.E u j w) := by
    apply Finset.sum_subset
    · intro w hw
      exact (hS w).2 (Finset.mem_filter.1 hw).2
    · intro w hw hn
      have : w ∉ L.supp := fun h => hn (Finset.mem_filter.2 ⟨h, (hS w).1 hw⟩)
      rw [L.E_supp u j w this]
      simp [SizeData₂.sz]
  set a : ℝ := (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) + FTypeG D j +
    c.g * (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) with ha
  have h2 : ∀ w ∈ S, SizeData₂.sz w (L.E u j w) =
      2 * a * (lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ)) +
      ∑ τ : D.what₂.Tau, nuAbs D u j τ * (2 * SizeData₂.lwP w * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) := by
    intro w hw
    have hw := (hS w).1 hw
    have hT : D.what₂.places.resChar w ≠ (D.mem u).A.T := hw ▸ host_g_ne_mem_A_T X u i
    have h3 : L.E u j w = (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) + EatG L X c i u j w := by
      rw [hE u j hj w]
      unfold Eval
      simp only [if_neg hT]
      fin_cases i
      · rw [if_pos (by simpa using hw), hw]; rfl
      · rw [if_neg (by rw [hw]; exact fun h => D.host.g_ne h.symm), if_pos (by simpa using hw), hw]; rfl
    have he : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by
      exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    have h4 : ∑ τ : D.what₂.Tau, nuAbs D u j τ * (2 * SizeData₂.lwP w * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) =
        2 * SizeData₂.lwP w * ∑ τ : D.what₂.Tau, nuAbs D u j τ * (vAdd (D.plEq w) (tauPib X i τ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [h3, h4, ha]
    unfold SizeData₂.sz EatG vNN Formalism.MainNotions.G.Nm SizeData₂.lwP
    field_simp
    ring
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum,
    factEtaMean D _ (D.host.g_prime i) S hS, Finset.sum_comm]
  have h5 : ∀ τ ∈ (Finset.univ : Finset D.what₂.Tau),
      ∑ w ∈ S, nuAbs D u j τ * (2 * SizeData₂.lwP w * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) =
        nuAbs D u j τ * Real.log (D.host.g i) := by
    intro τ _
    rw [← Finset.mul_sum, sum_half D _ (D.host.g_prime i) S hS _ (tauPib_norm X i τ)]
  rw [Finset.sum_congr rfl h5, ← Finset.sum_mul, ha]
  unfold FTypeG
  ring

theorem padic_log_le (p n : ℕ) (hp : p.Prime) : (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn pow_padicValNat_dvd
    rw [← Real.log_pow]
    apply Real.log_le_log
    · have := hp.pos
      positivity
    · exact_mod_cast h

theorem arith_bound (δ v e lg f m b L N η C₁ C₂ cg CY B : ℝ) (hB : B = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hCY : 0 ≤ CY) (hδ : |δ| ≤ C₁ * f * b) (hv0 : 0 ≤ v)
    (hv : v ≤ C₂ * f * N * Real.log (f * N)) (he : e = cg * f * (N ^ 2 + m ^ 2 * η)) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ (CY + 1) * L) (hη0 : 0 ≤ η) (hNη : N ^ 2 ≤ η) (hmf : m ≤ f) (hfη : f * η ≤ b) :
    |δ * lg + 2 * v + 2 * e * lg| ≤ (|C₁| * (CY + 1) + 2 * |C₂| + 4 * |cg| * (CY + 1)) * B := by
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hηb : η ≤ b := le_trans (le_mul_of_one_le_left hη0 hf) hfη
  have hb : 0 ≤ b := hη0.trans hηb
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have hB1 : f * b * L ≤ B := by
    have : B = m * (f * b * L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (mul_nonneg hfb hL0) hm
  have hB2 : f * b ≤ B := le_trans (le_mul_of_one_le_right hfb hL) hB1
  have t1 : |δ * lg| ≤ |C₁| * (CY + 1) * B := by
    rw [abs_mul, abs_of_nonneg hlg0]
    have h1 : |δ| ≤ |C₁| * (f * b) := by
      refine hδ.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hfb
    calc |δ| * lg ≤ |C₁| * (f * b) * ((CY + 1) * L) := mul_le_mul h1 hlg hlg0 (by positivity)
      _ = |C₁| * (CY + 1) * (f * b * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : v ≤ |C₂| * B := by
    have hfN : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf hN
    have l0 : 0 ≤ Real.log (f * N) := Real.log_nonneg hfN
    have l1 : Real.log (f * N) ≤ f * N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h1 : f * N * Real.log (f * N) ≤ B := by
      calc f * N * Real.log (f * N) ≤ f * N * (f * N) := mul_le_mul_of_nonneg_left l1 (by linarith)
        _ = f * (f * N ^ 2) := by ring
        _ ≤ f * b := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hNη hf0).trans hfη) hf0
        _ ≤ B := hB2
    calc v ≤ C₂ * (f * N * Real.log (f * N)) := by rw [← mul_assoc, ← mul_assoc]; exact hv
      _ ≤ |C₂| * (f * N * Real.log (f * N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (by linarith) l0)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have t3 : |2 * e * lg| ≤ 4 * |cg| * (CY + 1) * B := by
    have h0 : 0 ≤ N ^ 2 + m ^ 2 * η := by positivity
    have h1 : N ^ 2 + m ^ 2 * η ≤ 2 * (m * b) := by
      have a1 : m * η ≤ b := (mul_le_mul_of_nonneg_right hmf hη0).trans hfη
      have a2 : m * (m * η) ≤ m * b := mul_le_mul_of_nonneg_left a1 hm0
      have a3 : b ≤ m * b := le_mul_of_one_le_left hb hm
      nlinarith
    have h2 : |2 * e * lg| = 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) := by
      rw [he, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlg0, abs_of_nonneg h0, abs_of_nonneg hf0]
      simp only [abs_two]
      ring
    rw [h2]
    calc 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) ≤ 2 * |cg| * f * (2 * (m * b) * ((CY + 1) * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hlg hlg0 (by positivity)) (by positivity)
      _ = _ := by rw [hB]; ring
  have tri : |δ * lg + 2 * v + 2 * e * lg| ≤ |δ * lg| + |2 * v| + |2 * e * lg| := abs_add_three _ _ _
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * v)] at tri
  nlinarith

theorem bound_one {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (hE : L.EDef X K c)
    (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (i : Fin 2) (C₁ C₂ A : ℝ)
    (h1 : |(∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ) - A| ≤ C₁ * D.R.f * L.sc.b)
    (h2 : FactDGam D C₂) :
    |∑ w ∈ L.supp.filter (fun w => D.what₂.places.resChar w = D.host.g i), SizeData₂.sz w (L.E u j w) -
      A * Real.log (D.host.g i)| ≤ (|C₁| * (P.CYL + 1) + 2 * |C₂| + 4 * |c.g| * (P.CYL + 1)) * L.B0 := by
  rw [sum_over_g hE u j hj i]
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast hmfn
  have hf : (1 : ℝ) ≤ D.R.f := hm.trans hmf
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b := by
    have a1 := P.eta_le
    rw [le_div_iff₀ (by positivity)] at a1
    have a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)
    have a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) a2
    calc _ ≤ _ := a3
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ _ := a1
  have hg0 : (0 : ℝ) < D.host.g i := by exact_mod_cast (D.host.g_prime i).pos
  have hlg0 : 0 ≤ Real.log (D.host.g i) := Real.log_natCast_nonneg _
  have hlg : Real.log (D.host.g i) ≤ (P.CYL + 1) * L.sc.L := by
    obtain ⟨Y, -, -, hY, hg⟩ := P.g_Y
    have hY0 : 0 < Y := by linarith [(hg i).2]
    have a1 : Real.log (D.host.g i) ≤ Real.log (2 * Y) := Real.log_le_log hg0 (hg i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at a1
    have a2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have key := arith_bound ((∑ τ : D.what₂.Tau, nuAbs D u j τ) - (fockDeg D j : ℝ) - A)
    ((padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ) * Real.log (D.host.g i)) _ (Real.log (D.host.g i))
    D.R.f D.R.m L.sc.b L.sc.L (D.R.N D.R.m) L.etaSz C₁ C₂ c.g P.CYL L.B0 rfl hf hm hL hN P.CYL_pos.le h1
    (mul_nonneg (Nat.cast_nonneg _) hlg0) ((padic_log_le _ _ (D.host.g_prime i)).trans (h2 u)) rfl hlg0 hlg
    hη0 hNη hmf hfη
  convert key using 2
  ring

end GlobalTheory.TypeLoss

end

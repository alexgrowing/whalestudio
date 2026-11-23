import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralClosurePlaceRingsDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormScaleConjugateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProdNormEmbeddingsEqAbsNorm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

namespace OfAdelic

open UnitChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

theorem homog_pow {a : MRing ι} {d : K → ℕ} (ha : IsMultiHomog a d) (n : ℕ) : IsMultiHomog (a ^ n) (n • d) := by
  induction n with
  | zero => simpa using (homog_zero_deg_one (K := K) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih ha

theorem notMem_of_aeval_ne {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hm
  have h0 : mConeMap y f = 0 := hm
  have h1 := aeval_scaled y (fun _ => 1) f
  rw [h0] at h1
  simp only [mul_one, map_zero] at h1
  exact hf h1

theorem adjoin_segre_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.adjoin ℤ (Set.range fun j : (∀ k, ι k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) = chartRingZ y c := by
  classical
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨j, rfl⟩
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  · rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    simp only [← Finset.prod_div_distrib]
    rw [Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      rw [Function.update_of_ne hb, div_self (hc b)]
    · simp

theorem exists_forms_of_elem {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ) {α : F} (hα : α ≠ 0) :
    ∃ (d : K → ℕ) (P Q : MRing ι), IsMultiHomog P d ∧ IsMultiHomog Q d ∧ aeval y Q ≠ 0 ∧
      aeval y P = φ α * aeval y Q := by
  classical
  choose c hc using hO.1
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) α
  have hb : algebraMap (𝓞 F) F b ≠ 0 := (div_ne_zero_iff.1 hα).2
  have h1 : φ (algebraMap (𝓞 F) F a) ∈ chartRingZ y c := hO.2 c hc a
  have h2 : φ (algebraMap (𝓞 F) F b) ∈ chartRingZ y c := hO.2 c hc b
  obtain ⟨m, G, hG, e1⟩ := chart_form hc h1
  obtain ⟨m', G', hG', e2⟩ := chart_form hc h2
  have hY : ∀ n : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ n k) ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hφb : φ (algebraMap (𝓞 F) F b) ≠ 0 := (map_ne_zero φ).2 hb
  refine ⟨m + m', G * cMon c m', G' * cMon c m, homog_mul hG (homog_cMon c m'), ?_, ?_, ?_⟩
  · rw [add_comm m m']
    exact homog_mul hG' (homog_cMon c m)
  · rw [map_mul, aeval_cMon, ← e2]
    exact mul_ne_zero (mul_ne_zero hφb (hY _)) (hY _)
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, ← e1, ← e2, map_div₀]
    field_simp

theorem exists_forms_deg {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ) (hB : Birational y) (a : K → ℤ)
    (c₀ : Ω) : ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) - dh k = a k) ∧ aeval y h ≠ 0 ∧ aeval y g = c₀ * aeval y h := by
  classical
  choose c hc using hO.1
  obtain ⟨d, g, h, hg, hh, hne, e⟩ := hB (c₀ * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))
  let ap : K → ℕ := fun k => (a k).toNat
  let am : K → ℕ := fun k => (-a k).toNat
  have hpm : ∀ k, (ap k : ℤ) - am k = a k := fun k => by simp only [ap, am]; omega
  have hY : ∀ n : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ n k) ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d + ap, d + am, g * cMon c ap, h * cMon c am, homog_mul hg (homog_cMon c ap),
    homog_mul hh (homog_cMon c am), fun k => ?_, ?_, ?_⟩
  · have := hpm k
    simp only [Pi.add_apply]
    push_cast
    omega
  · rw [map_mul, aeval_cMon]
    exact mul_ne_zero hne (hY _)
  · have hZ := zpow_factor (a := ap) (b := am) (fun k => y ⟨k, c k⟩) hc
    simp only [hpm] at hZ
    rw [map_mul, map_mul, aeval_cMon, aeval_cMon, e, ← hZ]
    ring

theorem sum_log_of_val (r : HeightOneSpectrum (𝓞 F) →₀ ℚ) (M : ℕ) (α : F) (hα : α ≠ 0)
    (hval : ∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n))
    (hM : 0 < M) :
    ∑ σ : F →+* ℂ, Real.log ‖σ α‖ =
      M * r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  classical
  choose n hn1 hn2 using hval
  have hsupp : ∀ v, n v ≠ 0 → v ∈ r.support := fun v hv => by
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hv
    have := hn1 v
    rw [h0, mul_zero] at this
    exact_mod_cast this
  let n' : HeightOneSpectrum (𝓞 F) →₀ ℤ := Finsupp.onFinset r.support n hsupp
  have hn' : ∀ v, n' v = n v := fun v => rfl
  rw [sum_log_embeddings_eq F n' α hα (fun v => by rw [hn']; exact hn2 v),
    Finsupp.sum_of_support_subset n' (s := r.support) (fun v hv => hsupp v (by simpa [hn'] using hv)) _ (by simp),
    Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : (n v : ℝ) = M * (r v : ℝ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) (hn1 v)
  rw [hn', h]
  ring

section Model

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem inChart_ne {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

theorem exists_global {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {L : Lat ξ E} {e₀ : E} {c₀ : Ω} {a : K → ℤ}
    {r : HeightOneSpectrum (𝓞 F) →₀ ℚ}
    (hT : CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩)) (hN : NormalCpt ξ)
    (hD : L.IsDegOn Set.univ y a e₀) (hc0 : c₀ ≠ 0)
    (hloc : ∀ p : Cpt ξ, ((∀ a : F, φ a ∈ regAt ξ p) ∧ OrderAt L (c₀ • e₀) 1 1 0 p) ∨
      ∃ (v : HeightOneSpectrum (𝓞 F)) (π : F) (m : ℕ) (n : ℤ), (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p) ∧
        v.valuation F π = WithZero.exp (-1 : ℤ) ∧ 0 < m ∧ (n : ℚ) = m * r v ∧ OrderAt L (c₀ • e₀) (φ π) m n p) :
    ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧
      ∀ (c : ∀ k, ι k) (p : Cpt ξ), InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p →
        unitAt ξ p ((c₀ / ∏ k, y ⟨k, c k⟩ ^ a k) ^ M / φ α) := by
  classical
  have he₀ : e₀ ≠ 0 := hD.1
  have hBne : ∀ (c : ∀ k, ι k) (p : Cpt ξ), InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p →
      (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := fun c p h =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (inChart_ne h k)
  choose cp hcp using hT.cover
  have hL : ∀ p, L p = Submodule.span (regAt ξ p) {(∏ k, y ⟨k, cp p k⟩ ^ a k) • e₀} := fun p =>
    hD.2 p trivial (cp p) (hcp p)
  let s : Cpt ξ → Ω := fun p => c₀ / ∏ k, y ⟨k, cp p k⟩ ^ a k
  have hs0 : ∀ p, s p ≠ 0 := fun p => div_ne_zero hc0 (hBne _ p (hcp p))
  have hσ : ∀ p, c₀ • e₀ = s p • (∏ k, y ⟨k, cp p k⟩ ^ a k) • e₀ := fun p => by
    rw [smul_smul, div_mul_cancel₀ _ (hBne _ p (hcp p))]
  have hpl : ∀ p : Cpt ξ, ∃ o : Option (HeightOneSpectrum (𝓞 F)),
      (o = none → (∀ a : F, φ a ∈ regAt ξ p) ∧ OrderAt L (c₀ • e₀) 1 1 0 p) ∧
      ∀ v, o = some v → ∃ (π : F) (m : ℕ) (n : ℤ), (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p) ∧
        v.valuation F π = WithZero.exp (-1 : ℤ) ∧ 0 < m ∧ (n : ℚ) = m * r v ∧
        OrderAt L (c₀ • e₀) (φ π) m n p := fun p => by
    rcases hloc p with h | ⟨v, π, m, n, h⟩
    · exact ⟨none, fun _ => h, fun v hv => by simp at hv⟩
    · refine ⟨some v, fun h' => by simp at h', fun w hw => ?_⟩
      obtain rfl : v = w := by simpa using hw
      exact ⟨π, m, n, h⟩
  choose pl hpl1 hpl2 using hpl
  obtain ⟨M, α, hM, hα, hv, hx⟩ := GlobalTheory.T.exists_pow_section_associated_global_element F Ω (Cpt ξ) φ (regAt ξ) s pl r
    (fun p z hz => hN p z hz)
    (fun p hp => by
      obtain ⟨h1, h2⟩ := hpl1 p hp
      have hu := h2.unitAt (hL p) (hσ p)
      simp only [pow_one, zpow_zero, div_one] at hu
      exact ⟨h1, hu.2.1, hu.1, hu.2.2⟩)
    (fun p v hp => by
      obtain ⟨π, m, n, h1, h2, h3, h4, h5⟩ := hpl2 p v hp
      have hu := h5.unitAt (hL p) (hσ p)
      refine ⟨h1, m, n, π, h3, h4, h2, hs0 p, hu.2.1, ?_⟩
      have := hu.2.2
      rwa [inv_div] at this)
  refine ⟨M, α, hM, hα, hv, fun c p hc => ?_⟩
  have hφα : φ α ≠ 0 := (map_ne_zero φ).2 hα
  have hne : (∏ k, y ⟨k, c k⟩ ^ a k) • e₀ ≠ 0 := smul_ne_zero (hBne c p hc) he₀
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq hne ((hD.2 p trivial c hc).symm.trans (hL p))
  have hB : (∏ k, y ⟨k, c k⟩ ^ a k) = u * ∏ k, y ⟨k, cp p k⟩ ^ a k := by
    apply smul_left_injective Ω he₀
    simp only [mul_smul]
    exact e
  have hU : unitAt ξ p (s p ^ M / φ α) :=
    ⟨div_ne_zero (pow_ne_zero _ (hs0 p)) hφα, (hx p).1, by rw [inv_div]; exact (hx p).2⟩
  have : (c₀ / ∏ k, y ⟨k, c k⟩ ^ a k) ^ M / φ α = s p ^ M / φ α * u⁻¹ ^ M := by
    have h1 := hBne _ p (hcp p)
    have h2 := hu.1
    have h3 : c₀ / (u * ∏ k, y ⟨k, cp p k⟩ ^ a k) = s p * u⁻¹ := by
      simp only [s]
      field_simp
    rw [hB, h3, mul_pow]
    ring
  rw [this]
  exact ZUnit.mul hU (ZUnit.pow (ZUnit.inv hu) M)

theorem unit_chartRing {y : (Σ k, ι k) → Ω} (hT : CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩))
    {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {w : Ω}
    (h : ∀ p : Cpt ξ, InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p → unitAt ξ p w) :
    w ∈ chartRingZ y c ∧ w⁻¹ ∈ chartRingZ y c := by
  have hx : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hr := hT.ring c hx
  rw [adjoin_segre_eq y c hc] at hr
  exact ⟨(hr w).2 fun p hp => (h p hp).2.1, (hr w⁻¹).2 fun p hp => (h p hp).2.2⟩

end Model

end OfAdelic

open OfAdelic UnitChart in

theorem exists_flatHerm_of_adelic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (e₀ : E) (c₀ : Ω) (A : HermLine ι) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ) (cinf : (F →+* ℂ) → ℝ), OverInt y φ → Birational y → IsConjInvariantH A → CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → NormalCpt ξ → L.IsDegOn Set.univ y A.a e₀ → c₀ ≠ 0 → (∀ p : Cpt ξ, ((∀ a : F, φ a ∈ regAt ξ p) ∧ OrderAt L (c₀ • e₀) 1 1 0 p) ∨ ∃ (v : HeightOneSpectrum (𝓞 F)) (π : F) (m : ℕ) (n : ℤ), (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p) ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ 0 < m ∧ (n : ℚ) = m * r v ∧ OrderAt L (c₀ • e₀) (φ π) m n p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F →+* ℂ) z (g h : MRing ι) (dg dh : K → ℕ), PtOver y φ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → ∃ S : FlatHerm y φ A, S.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F : ℝ) := by
  intro K _ ι _ Ω _ F _ _ y φ X ξ E _ _ L e₀ c₀ A r cinf hO hB hC hT hN hD hc0 hloc hcinf hnorm
  classical
  obtain ⟨M, α, hM, hα, hval, hU⟩ := exists_global hT hN hD hc0 hloc
  obtain ⟨dg, dh, g, h, hg, hh, hd, hh0, hgh⟩ := exists_forms_deg hO hB A.a c₀
  obtain ⟨d, P, Q, hP, hQ, hQ0, hPQ⟩ := exists_forms_of_elem hO hα
  have hφα : φ α ≠ 0 := (map_ne_zero φ).2 hα
  have hg0 : aeval y g ≠ 0 := by rw [hgh]; exact mul_ne_zero hc0 hh0
  have hP0 : aeval y P ≠ 0 := by rw [hPQ]; exact mul_ne_zero hφα hQ0
  have hf0 : aeval y (g ^ M * Q) ≠ 0 := by
    rw [map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hg0) hQ0
  have hgg0 : aeval y (h ^ M * P) ≠ 0 := by
    rw [map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hh0) hP0
  have hfH : IsMultiHomog (g ^ M * Q) (M • dg + d) := homog_mul (homog_pow hg M) hQ
  have hgH : IsMultiHomog (h ^ M * P) (M • dh + d) := homog_mul (homog_pow hh M) hP
  have hdeg : ∀ k, ((M • dg + d) k : ℤ) - ((M • dh + d) k : ℕ) = M * A.a k := fun k => by
    rw [← hd k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hunit : IsUnitSec (mCoordIdeal y) (g ^ M * Q) (h ^ M * P) := by
    refine (isUnitSec_iff_chart K ι Ω y _ _ _ _ hO.1 hfH hgH (notMem_of_aeval_ne hf0)
      (notMem_of_aeval_ne hgg0)).2 fun c hc => ?_
    have hBc : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have hw : aeval y (g ^ M * Q) / aeval y (h ^ M * P) *
        ∏ k, y ⟨k, c k⟩ ^ (-(((M • dg + d) k : ℤ) - ((M • dh + d) k : ℕ))) =
        (c₀ / ∏ k, y ⟨k, c k⟩ ^ A.a k) ^ M / φ α := by
      have hprod : (∏ k, y ⟨k, c k⟩ ^ (-(((M • dg + d) k : ℤ) - ((M • dh + d) k : ℕ)))) =
          ((∏ k, y ⟨k, c k⟩ ^ A.a k) ^ M)⁻¹ := by
        rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hdeg k, zpow_neg, mul_comm, zpow_mul, zpow_natCast]
      rw [hprod, map_mul, map_mul, map_pow, map_pow, hgh, hPQ, mul_pow, div_pow]
      field_simp
    rw [hw]
    exact unit_chartRing hT hc fun p hp => hU c p hp
  have hnα : ∀ σ : F →+* ℂ, 0 < ‖σ α‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hα)
  let κ : (F →+* ℂ) → ℝ := fun σ => cinf σ / ‖σ α‖ ^ ((M : ℝ)⁻¹)
  have hκ_pos : ∀ σ, 0 < κ σ := fun σ => div_pos (hcinf σ) (Real.rpow_pos_of_pos (hnα σ) _)
  have hκM : ∀ σ, κ σ ^ M * ‖σ α‖ = cinf σ ^ M := fun σ => by
    simp only [κ]
    rw [div_pow, Real.rpow_inv_natCast_pow (hnα σ).le hM.ne']
    exact div_mul_cancel₀ _ (hnα σ).ne'
  have hnorm' : ∀ σ z, PtOver y φ σ z → ‖evC z (g ^ M * Q)‖ = (κ σ * A.h z) ^ M * ‖evC z (h ^ M * P)‖ := by
    intro σ z hz
    have h1 := hnorm σ z g h dg dh hz hg hh hd hgh
    have h2 := hz.2 α d P Q hP hQ hPQ
    simp only [evC, map_mul, map_pow, norm_mul, norm_pow] at h1 h2 ⊢
    rw [h1, h2, norm_mul, mul_pow, mul_pow, ← hκM σ]
    ring
  let S : FlatHerm y φ A :=
    { M := M, M_pos := hM, f := g ^ M * Q, g := h ^ M * P, df := M • dg + d, dg := M • dh + d, hf := hfH, hg := hgH
      deg := hdeg, f_ne := notMem_of_aeval_ne hf0, g_ne := notMem_of_aeval_ne hgg0, unit := hunit, κ := κ
      κ_pos := hκ_pos
      κ_conj := GlobalTheory.T.norm_scale_conjugate_invariant K ι Ω F y φ A M _ _ _ κ hO hM hgH (notMem_of_aeval_ne hgg0) hC hκ_pos hnorm'
      norm := hnorm' }
  refine ⟨S, ?_⟩
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hlog : ∀ σ, Real.log (κ σ) = Real.log (cinf σ) - (M : ℝ)⁻¹ * Real.log ‖σ α‖ := fun σ => by
    simp only [κ]
    rw [Real.log_div (hcinf σ).ne' (Real.rpow_pos_of_pos (hnα σ) _).ne', Real.log_rpow (hnα σ)]
  have hsum := sum_log_of_val r M α hα hval hM
  change -((∑ σ, Real.log (κ σ)) / (Module.finrank ℚ F : ℝ)) = _
  simp only [hlog]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, inv_mul_cancel_left₀ hMne]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat

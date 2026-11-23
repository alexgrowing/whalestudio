import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomRoots
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCharpolyRootLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormDehomRoots

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eval_mConeMap (y : (Σ k, ι k) → Ω) (t : K → Ω) (f : MRing ι) :
    MvPolynomial.eval t (mConeMap y f) = aeval (fun p => y p * t p.1) f := by
  rw [mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  rw [← eval_mConeMap, ProjLine.mConeMap_eq_of_isMultiHomog y hg, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal y) (t : K → Ω) :
    aeval (fun p => y p * t p.1) f = 0 := by
  rw [← eval_mConeMap, RingHom.mem_ker.1 hf, map_zero]

omit [Fintype K] in

theorem isMultiHomog_monomial {ν : (Σ k, ι k) →₀ ℕ} {d : K → ℕ} (h : ∀ k, ∑ i, ν ⟨k, i⟩ = d k) :
    IsMultiHomog (monomial ν (1 : ℤ)) d := by
  intro m hm k
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  exact h k

omit [Fintype K] in

theorem sum_single_block (k : K) (i₀ i₁ : ι k) (k' : K) :
    ∑ i, (Finsupp.single (⟨k, i₀⟩ : Σ k, ι k) 1) ⟨k', i⟩ =
      ∑ i, (Finsupp.single (⟨k, i₁⟩ : Σ k, ι k) 1) ⟨k', i⟩ := by
  classical
  by_cases h : k = k'
  · subst h
    simp [Finsupp.single_apply]
  · have h0 : ∀ (i₂ : ι k) (i : ι k'), (Finsupp.single (⟨k, i₂⟩ : Σ k, ι k) 1) ⟨k', i⟩ = 0 := fun i₂ i => by
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact h (congrArg Sigma.fst h')
    simp only [h0, Finset.sum_const_zero]

theorem aeval_mem_chartLatNm {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g ∈ chartLatNm y (fun k => ((1 * d k : ℕ) : ℤ)) 1 := by
  intro c _
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((1 * d k : ℕ) : ℤ))) =
      ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, one_mul, one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹)]
  have hmem : aeval (fun p => y p * (y ⟨p.1, c p.1⟩)⁻¹) g ∈ chartRingZ y c := by
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
    refine ⟨g, ?_⟩
    simp only [div_eq_mul_inv]
    rfl
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (x := (⟨_, hmem⟩ : chartRingZ y c))

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ringHom_aeval {A A' σ : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] [Algebra ℤ A'] (φ : A →+* A')
    (x : σ → A)
    (f : MvPolynomial σ ℤ) : φ (aeval x f) = aeval (fun p => φ (x p)) f := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ringHom_aeval_eq_eval {A A' σ : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] (φ : A →+* A')
    (x : σ → A)
    (f : MvPolynomial σ ℤ) : φ (aeval x f) = eval (fun p => φ (x p)) (map (Int.castRingHom A') f) := by
  rw [eval_map, aeval_def, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem field_ratio {F : Type*} [Field F] {x₁ c l : F} (p : F) (h₁ : x₁ ≠ 0) (hc : c ≠ 0) (hl : l ≠ 0) :
    x₁ * p / l ^ (1 * 1) / (x₁ * c / l ^ (1 * 1)) = p * c⁻¹ := by
  field_simp

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem field_chart {F : Type*} [Field F] {lb la E : F} (hl : la ≠ 0) : lb * E = lb / la * (la * E) := by
  field_simp

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem field_section {F : Type*} [Field F] {s H Ph Pe la : F} (m : ℕ) (hl : la ≠ 0) :
    s * H * (Ph * Pe ^ m) = s / la ^ m * (la * Pe) ^ m * (H * Ph) := by
  field_simp
  ring

abbrev chartClosure (y : (Σ k, ι k) → Ω) [CharZero Ω] {D : ℕ} (L : Fin (D + 1) → MRing ι) (a : Fin (D + 1)) :
    Subalgebra (Algebra.adjoin ℚ (Set.range fun k => aeval y (L k) / aeval y (L a))) Ω :=
  integralClosure (Algebra.adjoin ℚ (Set.range fun k => aeval y (L k) / aeval y (L a))) Ω

set_option maxHeartbeats 1600000 in

theorem proof (hG : PullFormsGeneric.Statement) (hS : PullSectionIntegral.Statement)
    (hR : CharpolyRootLift.Statement) : FibreNormDehomRoots.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hA hB he hLe hnz τ s hs j c hc ζ hζ w hw
  obtain ⟨hLj, hfd, hc0, hhom, hchar⟩ := hc
  have := hfd
  have hgen := hG K ι Ω y D e L hA hB he hLe hnz
  obtain ⟨a, ha⟩ : ∃ a, ζ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hζ (funext h)
  have hla : aeval y (L a) ≠ 0 := fun h0 =>
    X_ne_zero a (hgen 1 (X a) (isHomogeneous_X ℚ a) (by rw [aeval_X]; exact h0))
  have hu : s / aeval y (L a) ^ (q * τ) ∈ chartClosure y L a := hS K ι Ω y D e L q hA hB he hLe hnz τ s hs a hla
  obtain ⟨ψ, hψl, hψu⟩ := hR Ω D (fun i => aeval y (L i)) (pullField y L) rfl hgen j (q * τ) s c hLj hc0
    hhom hchar a hu ζ ha w hw

  have memM : ∀ g : MRing ι, IsMultiHomog g e → aeval y g / aeval y (L a) ^ (1 * 1) ∈ chartClosure y L a :=
    fun g hg => hS K ι Ω y D e L 1 hA hB he hLe hnz 1 (aeval y g) (aeval_mem_chartLatNm hg) a hla
  have memL : ∀ b, aeval y (L b) / aeval y (L a) ∈ chartClosure y L a := fun b =>
    (mem_integralClosure_iff _ _).2 (isIntegral_algebraMap
      (x := (⟨_, Algebra.subset_adjoin ⟨b, rfl⟩⟩ : Algebra.adjoin ℚ (Set.range fun k => aeval y (L k) / aeval y (L a)))))

  have hsplit : ∀ (g : MRing ι) (hg : IsMultiHomog g e),
      (⟨aeval y g / aeval y (L a) ^ (1 * 1), memM g hg⟩ : chartClosure y L a) =
        ∑ x ∈ g.support.attach, ((coeff x.1 g : ℤ) : chartClosure y L a) *
          ⟨aeval y (monomial x.1 (1 : ℤ)) / aeval y (L a) ^ (1 * 1), memM _ (isMultiHomog_monomial (hg x.1 x.2))⟩ := by
    intro g hg
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubringClass.coe_intCast]
    rw [Finset.sum_attach g.support (fun x => ((coeff x g : ℤ) : Ω) *
      (aeval y (monomial x (1 : ℤ)) / aeval y (L a) ^ (1 * 1)))]
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [aeval_monomial, map_one, one_mul, algebraMap_int_eq, eq_intCast, mul_div_assoc]
  obtain ⟨ν, hν, hψv⟩ : ∃ (ν : (Σ k, ι k) →₀ ℕ) (hν : ν ∈ (L a).support),
      ψ ⟨aeval y (monomial ν (1 : ℤ)) / aeval y (L a) ^ (1 * 1),
        memM _ (isMultiHomog_monomial (hLe a ν hν))⟩ ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : (⟨aeval y (L a) / aeval y (L a) ^ (1 * 1), memM _ (hLe a)⟩ : chartClosure y L a) = 1 :=
      Subtype.ext (by
        show aeval y (L a) / aeval y (L a) ^ (1 * 1) = 1
        rw [mul_one, pow_one, div_self hla])
    have h2 := congrArg ψ ((hsplit (L a) (hLe a)).symm.trans h1)
    rw [map_one, map_sum] at h2
    simp only [map_mul, map_intCast] at h2
    rw [Finset.sum_eq_zero (fun x _ => by rw [h x.1 x.2, mul_zero])] at h2
    exact zero_ne_one h2
  obtain ⟨v, hvv, hψv⟩ : ∃ v : chartClosure y L a,
      (v : Ω) = aeval y (monomial ν (1 : ℤ)) / aeval y (L a) ^ (1 * 1) ∧ ψ v ≠ 0 := ⟨_, rfl, hψv⟩
  have hsum : ∀ k, ∑ i, ν ⟨k, i⟩ = e k := hLe a ν hν
  have hcc : ∀ k, ∃ i, ν ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := fun i => ν ⟨k, i⟩) (by rw [hsum k]; exact Nat.one_le_iff_ne_zero.1 (he k))
    exact ⟨i, hi⟩
  choose cc hcc using hcc
  have hν1 : ∀ k, (ν - Finsupp.single ⟨k, cc k⟩ 1) + Finsupp.single ⟨k, cc k⟩ 1 = ν := fun k =>
    tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (hcc k)))
  have hmon : ∀ k, aeval y (monomial ν (1 : ℤ)) =
      aeval y (monomial (ν - Finsupp.single ⟨k, cc k⟩ 1) (1 : ℤ)) * y ⟨k, cc k⟩ := fun k => by
    conv_lhs => rw [← hν1 k]
    rw [monomial_add_single, pow_one, map_mul, aeval_X]
  have hyν : aeval y (monomial ν (1 : ℤ)) ≠ 0 := fun h0 => hψv (by
    rw [show v = 0 from Subtype.ext (by rw [hvv, h0, zero_div]; rfl), map_zero])
  have hyk : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k h0 => hyν (by rw [hmon k, h0, mul_zero])
  have hy1 : ∀ k, aeval y (monomial (ν - Finsupp.single ⟨k, cc k⟩ 1) (1 : ℤ)) ≠ 0 := fun k h0 =>
    hyν (by rw [hmon k, h0, zero_mul])
  have hsum' : ∀ (p : Σ k, ι k) (k' : K),
      ∑ i, ((ν - Finsupp.single ⟨p.1, cc p.1⟩ 1) + Finsupp.single p 1 : (Σ k, ι k) →₀ ℕ) (⟨k', i⟩ : Σ k, ι k) = e k' := by
    rintro ⟨k₀, i₀⟩ k'
    have h1 := congrArg (fun μ : (Σ k, ι k) →₀ ℕ => ∑ i, μ ⟨k', i⟩) (hν1 k₀)
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1 ⊢
    rw [sum_single_block k₀ i₀ (cc k₀) k', h1, hsum k']
  have hr : ∀ p : Σ k, ι k, ∃ r : chartClosure y L a, (r : Ω) =
      aeval y (monomial (ν - Finsupp.single ⟨p.1, cc p.1⟩ 1) (1 : ℤ)) * y p / aeval y (L a) ^ (1 * 1) :=
    fun p => ⟨(⟨_, memM _ (isMultiHomog_monomial (hsum' p))⟩ : chartClosure y L a), by
      show aeval y _ / _ = _
      rw [monomial_add_single, pow_one, map_mul, aeval_X]⟩
  choose r hr using hr

  have hpow : ∀ {F : Type} [Field F] (g : chartClosure y L a →+* F), g v ≠ 0 →
      ∀ t : Submonoid.powers v, IsUnit (g t) := fun g hg t => by
    obtain ⟨n, hn⟩ := t.2
    rw [← hn, map_pow]
    exact (isUnit_iff_ne_zero.2 hg).pow n
  have hv0 : (algebraMap (chartClosure y L a) Ω) v ≠ 0 := by
    show (v : Ω) ≠ 0
    rw [hvv]
    exact div_ne_zero hyν (pow_ne_zero _ hla)
  let ψ' : Localization.Away v →+* ℂ := IsLocalization.lift (hpow ψ hψv)
  let ι' : Localization.Away v →+* Ω := IsLocalization.lift (hpow (algebraMap (chartClosure y L a) Ω) hv0)
  have hinj : Function.Injective ι' := by
    intro x₁ x₂ h12
    obtain ⟨⟨a₁, s₁⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.Away v) (Submonoid.powers v) x₁
    obtain ⟨⟨a₂, s₂⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.Away v) (Submonoid.powers v) x₂
    rw [IsLocalization.mk'_eq_iff_eq]
    congr 1
    have e1 := (IsLocalization.lift_mk'_spec (S := Localization.Away v) (hpow (algebraMap (chartClosure y L a) Ω) hv0) a₁ _ s₁).1 rfl
    have e2 := (IsLocalization.lift_mk'_spec (S := Localization.Away v) (hpow (algebraMap (chartClosure y L a) Ω) hv0) a₂ _ s₂).1 rfl
    have key : (algebraMap (chartClosure y L a) Ω) (↑s₂ * a₁) =
        (algebraMap (chartClosure y L a) Ω) (↑s₁ * a₂) := by
      rw [map_mul, map_mul, e1, e2]
      change _ * (_ * ι' _) = _ * (_ * ι' _)
      rw [h12]
      ring
    exact Subtype.val_injective key
  have hι_mk : ∀ x : chartClosure y L a,
      ι' (IsLocalization.mk' _ x (⟨v, Submonoid.mem_powers v⟩ : Submonoid.powers v)) = (x : Ω) / v := fun x =>
    (IsLocalization.lift_mk'_spec _ _ _ _).2 (by
      show (x : Ω) = (v : Ω) * ((x : Ω) / v)
      have : (v : Ω) ≠ 0 := hv0
      field_simp)
  have hι_alg : ∀ x : chartClosure y L a, ι' (algebraMap _ _ x) = x := fun x => IsLocalization.lift_eq _ x
  have hψ_alg : ∀ x : chartClosure y L a, ψ' (algebraMap _ _ x) = ψ x := fun x => IsLocalization.lift_eq _ x

  let xc : (Σ k, ι k) → Localization.Away v := fun p =>
    IsLocalization.mk' _ (r p) (⟨v, Submonoid.mem_powers v⟩ : Submonoid.powers v)
  have hιxc : ∀ p, ι' (xc p) = y p * (y ⟨p.1, cc p.1⟩)⁻¹ := fun p => by
    show ι' (IsLocalization.mk' _ (r p) _) = _
    rw [hι_mk, hr, hvv, hmon p.1]
    exact field_ratio _ (hy1 p.1) (hyk p.1) hla
  let z : (Σ k, ι k) → ℂ := fun p => ψ' (xc p)
  have hιF : ∀ f : MRing ι, ι' (aeval xc f) = aeval (fun p => y p * (y ⟨p.1, cc p.1⟩)⁻¹) f := fun f => by
    rw [ringHom_aeval]
    simp only [hιxc]
  have hψF : ∀ f : MRing ι, ψ' (aeval xc f) = eval z (map (Int.castRingHom ℂ) f) := fun f =>
    ringHom_aeval_eq_eval ψ' xc f
  have hz : z ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => ⟨cc k, ?_⟩, fun f hf => ?_⟩
    · show ψ' (xc ⟨k, cc k⟩) ≠ 0
      rw [hinj (show ι' (xc ⟨k, cc k⟩) = ι' 1 by rw [hιxc, map_one, mul_inv_cancel₀ (hyk k)]), map_one]
      exact one_ne_zero
    · have h0 : ι' (aeval xc f) = ι' 0 := by rw [map_zero]; exact (hιF f).trans (aeval_eq_zero_of_mem hf (fun k => (y ⟨k, cc k⟩)⁻¹))
      rw [← hψF, hinj h0, map_zero]

  have hLb : ∀ b, eval z (map (Int.castRingHom ℂ) (L b)) = ζ b / ζ a * ψ' (aeval xc (L a)) := fun b => by
    have e : ι' (aeval xc (L b)) = ι' (algebraMap (chartClosure y L a) (Localization.Away v)
        (⟨_, memL b⟩ : chartClosure y L a) * aeval xc (L a)) := by
      rw [map_mul, hι_alg, hιF, hιF, aeval_scale (hLe b) y (fun k => (y ⟨k, cc k⟩)⁻¹),
        aeval_scale (hLe a) y (fun k => (y ⟨k, cc k⟩)⁻¹)]
      exact field_chart (lb := aeval y (L b)) (E := ∏ k, (y ⟨k, cc k⟩)⁻¹ ^ e k) hla
    rw [← hψF, hinj e, map_mul, hψ_alg, hψl b (memL b)]
  have hT : ψ' (aeval xc (L a)) ≠ 0 := by
    obtain ⟨b, hb⟩ := hnz z hz
    rw [hLb] at hb
    exact right_ne_zero_of_mul hb
  refine ⟨z, hz, ψ' (aeval xc (L a)) / ζ a, div_ne_zero hT ha, fun b => ?_, ?_⟩
  · rw [hLb]
    ring
  · intro dg dh g h hg hh hd hgh _
    have hprod : ∏ k, (y ⟨k, cc k⟩)⁻¹ ^ dg k =
        (∏ k, (y ⟨k, cc k⟩)⁻¹ ^ dh k) * (∏ k, (y ⟨k, cc k⟩)⁻¹ ^ e k) ^ (q * τ) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hd k, ← pow_mul, ← pow_add]
      congr 1
      ring
    have key : aeval xc g = algebraMap _ _ (⟨s / aeval y (L a) ^ (q * τ), hu⟩ : chartClosure y L a) *
        aeval xc (L a) ^ (q * τ) * aeval xc h := by
      apply hinj
      rw [map_mul, map_mul, map_pow, hιF, hιF, hιF, hι_alg, aeval_scale hg y (fun k => (y ⟨k, cc k⟩)⁻¹),
        aeval_scale hh y (fun k => (y ⟨k, cc k⟩)⁻¹), aeval_scale (hLe a) y (fun k => (y ⟨k, cc k⟩)⁻¹),
        hgh, hprod]
      exact field_section (s := s) (H := aeval y h) (la := aeval y (L a)) _ hla
    rw [← hψF, ← hψF, key, map_mul, map_mul, map_pow, hψ_alg, hψu, div_pow]
    ring

end FibreNormDehomRoots

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

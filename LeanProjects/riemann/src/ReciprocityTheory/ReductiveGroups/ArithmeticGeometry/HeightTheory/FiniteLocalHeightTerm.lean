import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ArchimedeanLocalHeightTerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem finite_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hFx : d.translatedForm x F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.localHeightAtPrime h (d.wx x) c la * logNorm la =
      Real.log (gaussAbs (FinitePlace.mk la) F) -
        Real.log (gaussAbs (FinitePlace.mk la) (d.translatedForm x F)) +
        Real.log (FinitePlace.mk la κ) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0)
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hfin := (d.places_over_la hd h la c).1
  have hZ : ∀ w ∈ d.PlOver la c, d.ordMM c (d.Wres c w) (d.wx x c) =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra)).untopD 0 - (w (d.rationalBaseRow c)).untopD 0 := by
    intro w hw
    obtain ⟨hv, -, j0, hj0, hint, hunit⟩ := d.admissible_over_prime hd h la c w hw
    exact d.ordMinMax_at_good_place hd c w hv j0 hj0 hint hunit hmem (hx c)
  have hNla : d.localHeightAtPrime h (d.wx x) c la =
      (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) : ℝ) - (d.nLa h c la (d.rationalBaseRow c) : ℝ) := by
    unfold localHeightAtPrime nLa
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hZ w (hfin.mem_toFinset.1 hw)]; push_cast; ring

  have ha1'0 : a1' ≠ 0 := mul_ne_zero (by simpa using hκ3) ha10
  have hraS : algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0
  have hw0 : d.rationalBaseRow c ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero, zero_mul] at hkey2
    exact mul_ne_zero hFne hb20 (hinj (hkey2.symm.trans (map_zero _).symm))
  have p1 := d.pf_fin hd h c _ hraS a1' b1 ha1'0 hb10 hkey1 la
  have p2 := d.pf_fin hd h c _ hw0 (F' * b2) a2 (mul_ne_zero hFne hb20) ha20 hkey2 la

  set v := FinitePlace.mk la with hv
  have hg := congrArg (gaussAbs v) hpoly
  rw [gauss_abs_mul v _ _ (mul_ne_zero (by simpa using hκ) ha1'0) ha20,
    gauss_abs_mul v _ _ (by simpa using hκ) ha1'0, HeightMultiplicativity.gaussAbs_C,
    gauss_abs_mul v _ _ (mul_ne_zero hFx hb20) hb10,
    gauss_abs_mul v _ _ hFx hb20] at hg
  have hl := congrArg Real.log hg
  have hk0 : 0 < v κ := (FinitePlace.pos_iff).2 hκ
  have q1 := gauss_abs_pos_of_ne_zero v a1' ha1'0
  have q2 := gauss_abs_pos_of_ne_zero v a2 ha20
  have q3 := gauss_abs_pos_of_ne_zero v _ hFx
  have q4 := gauss_abs_pos_of_ne_zero v b2 hb20
  have q5 := gauss_abs_pos_of_ne_zero v b1 hb10
  have q6 := gauss_abs_pos_of_ne_zero v F' hFne
  rw [Real.log_mul (by positivity) q2.ne', Real.log_mul hk0.ne' q1.ne',
    Real.log_mul (by positivity) q5.ne', Real.log_mul q3.ne' q4.ne'] at hl
  rw [gauss_abs_mul v _ _ hFne hb20, Real.log_mul q6.ne' q4.ne'] at p2
  rw [hNla]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0

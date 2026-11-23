import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionMonomialGenerators

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Maps

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

def jK : MvPolynomial (Idx D j N) (X.Kl la) →+* Kp X la N :=
  MvPolynomial.eval₂Hom (algebraMap (X.Kl la) (Kp X la N)) fun p => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)

def jF : MvPolynomial (Idx D j N) B.KO →+* Kp X la N :=
  (jK X la N).comp (MvPolynomial.map (algebraMap B.KO (X.Kl la)))

theorem jK_C (a : X.Kl la) : jK X la N (MvPolynomial.C a) = algebraMap (X.Kl la) (Kp X la N) a := by
  simp [jK]

theorem jF_C (a : B.KO) :
    jF X la N (MvPolynomial.C a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a) := by
  simp [jF, jK_C]

theorem jK_map (q : Pol X la N) : jK X la N (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la)) q) =
    algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) q) := by
  have h : (jK X la N).comp (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la))) =
      (algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (Pol X la N) (Op X la N)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C, jK_C,
        ← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N), ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N),
        ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]
    · intro p
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X]
      unfold jK; rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  exact RingHom.congr_fun h q

theorem val_algebraMap (a : B.KO) : Valued.v (algebraMap B.KO (X.Kl la) a) = la.valuation B.KO a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' la a

theorem jF_C_mem (a : B.KO) (ha : la.valuation B.KO a ≤ 1) :
    jF X la N (MvPolynomial.C a) ∈ Set.range (algebraMap (Op X la N) (Kp X la N)) := by
  have hm : algebraMap B.KO (X.Kl la) a ∈ la.adicCompletionIntegers B.KO := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_algebraMap]; exact ha
  refine ⟨algebraMap (X.Ol la) (Op X la N) ⟨_, hm⟩, ?_⟩
  rw [jF_C, ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N),
    IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N)]
  rfl

theorem jF_monomial_mem (β : Idx D j N →₀ ℕ) :
    jF X la N (MvPolynomial.monomial β 1) ∈ Set.range (algebraMap (Op X la N) (Kp X la N)) := by
  refine ⟨β.prod fun p k => Tv X la N p ^ k, ?_⟩
  simp [jF, jK, MvPolynomial.eval₂_monomial, Finsupp.prod, map_prod, map_pow]

theorem val_le_one_of_mem {x : X.Kl la}
    (hx : algebraMap (X.Kl la) (Kp X la N) x ∈ Set.range (algebraMap (Op X la N) (Kp X la N))) : Valued.v x ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨s, hs⟩ := hx
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hlt; exact absurd hlt (by simp)
  have hinv : Valued.v x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
  have hm : x⁻¹ ∈ la.adicCompletionIntegers B.KO := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hinv.le
  have h1 : s * algebraMap (X.Ol la) (Op X la N) ⟨x⁻¹, hm⟩ = 1 := by
    apply IsFractionRing.injective (Op X la N) (Kp X la N)
    rw [map_mul, hs, ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N),
      IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N), ← map_mul, map_one]
    show algebraMap (X.Kl la) (Kp X la N) (x * x⁻¹) = 1
    rw [mul_inv_cancel₀ hx0, map_one]
  have hu : IsUnit (algebraMap (X.Ol la) (Op X la N) ⟨x⁻¹, hm⟩) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1)
  have hu' : IsUnit (⟨x⁻¹, hm⟩ : X.Ol la) := isUnit_of_map_unit (algebraMap (X.Ol la) (Op X la N)) _ hu
  have := (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.valuationSubring.integers (Valued.v : Valuation (X.Kl la) _))).mp hu'
  exact absurd this hinv.ne

theorem addVal_le_vAdd (p : MvPolynomial (Idx D j N) B.KO) (β : Idx D j N →₀ ℕ) (r : Op X la N) (hβ : p.coeff β ≠ 0)
    (hr : algebraMap (Op X la N) (Kp X la N) r = jF X la N p) :
    IsDiscreteValuationRing.addVal (Op X la N) r ≤ ((vAdd la (p.coeff β)).toNat : ℕ∞) := by
  classical

  obtain ⟨β0, hβ0, hmax⟩ := Finset.exists_max_image p.support (fun γ => la.valuation B.KO (p.coeff γ))
    ⟨β, MvPolynomial.mem_support_iff.mpr hβ⟩
  have hc0 : p.coeff β0 ≠ 0 := MvPolynomial.mem_support_iff.mp hβ0
  set c0 : B.KO := p.coeff β0 with hc0def
  have hle : ∀ γ, la.valuation B.KO (p.coeff γ) ≤ la.valuation B.KO c0 := by
    intro γ
    by_cases hγ : γ ∈ p.support
    · exact hmax γ hγ
    · rw [MvPolynomial.notMem_support_iff.mp hγ, map_zero]; exact zero_le

  have hq : MvPolynomial.map (algebraMap B.KO (X.Kl la)) (MvPolynomial.C c0⁻¹ * p) ∈
      Set.range (MvPolynomial.map (σ := Idx D j N) (algebraMap (X.Ol la) (X.Kl la))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro y hy
    obtain ⟨γ, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hy
    have hm : algebraMap B.KO (X.Kl la) (c0⁻¹ * p.coeff γ) ∈ la.adicCompletionIntegers B.KO := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_algebraMap, map_mul, map_inv₀]
      exact (inv_mul_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0))).mpr (hle γ)
    exact ⟨⟨_, hm⟩, by rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]; rfl⟩
  obtain ⟨q, hq⟩ := hq
  have hq1 : q.coeff β0 = 1 := by
    apply IsFractionRing.injective (X.Ol la) (X.Kl la)
    rw [← MvPolynomial.coeff_map, hq, MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, ← hc0def, inv_mul_cancel₀ hc0,
      map_one, map_one]
  have hqu : IsUnit (algebraMap (Pol X la N) (Op X la N) q) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N)]
    intro hmem
    have := (MvPolynomial.mem_map_C_iff (I := IsLocalRing.maximalIdeal (X.Ol la))).mp hmem β0
    rw [hq1] at this
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
  obtain ⟨uq, huq⟩ := hqu
  have hfac : jF X la N p = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) c0) *
      algebraMap (Op X la N) (Kp X la N) (uq : Op X la N) := by
    rw [huq, ← jK_map, hq, ← jF_C]
    show _ = jF X la N (MvPolynomial.C c0) * jF X la N (MvPolynomial.C c0⁻¹ * p)
    rw [← map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.Ol la)
  have hϖ' := Op.irreducible_map X la N hϖ
  set n : ℕ := (vAdd la (p.coeff β)).toNat with hn
  by_contra hlt
  rw [not_le] at hlt
  have hdvd : algebraMap (X.Ol la) (Op X la N) ϖ ^ (n + 1) ∣ r := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ', nsmul_one]
    exact Order.add_one_le_of_lt hlt
  obtain ⟨s, hs⟩ := hdvd
  have hϖ0 : (ϖ : X.Kl la) ≠ 0 := by
    intro h; exact hϖ.ne_zero (Subtype.ext h)
  have hmem : algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) c0 * ((ϖ : X.Kl la) ^ (n + 1))⁻¹) ∈
      Set.range (algebraMap (Op X la N) (Kp X la N)) := by
    refine ⟨s * ((uq⁻¹ : (Op X la N)ˣ) : Op X la N), ?_⟩
    have hϖK : algebraMap (X.Kl la) (Kp X la N) (ϖ : X.Kl la) =
        algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) ϖ) := by
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N)]
      rfl
    have hne : algebraMap (X.Kl la) (Kp X la N) (ϖ : X.Kl la) ≠ 0 := (map_ne_zero _).mpr hϖ0
    have h1 : algebraMap (Op X la N) (Kp X la N) (uq : Op X la N) *
        algebraMap (Op X la N) (Kp X la N) ((uq⁻¹ : (Op X la N)ˣ) : Op X la N) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := hr.symm.trans (congrArg (algebraMap (Op X la N) (Kp X la N)) hs)
    rw [hfac, map_mul (algebraMap (Op X la N) (Kp X la N)), map_pow, ← hϖK] at h2
    rw [map_mul (algebraMap (X.Kl la) (Kp X la N)), map_inv₀, map_pow, map_mul (algebraMap (Op X la N) (Kp X la N))]
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hne)]
    calc _ = (algebraMap (X.Kl la) (Kp X la N) (ϖ : X.Kl la) ^ (n + 1) * algebraMap (Op X la N) (Kp X la N) s) *
          algebraMap (Op X la N) (Kp X la N) ((uq⁻¹ : (Op X la N)ˣ) : Op X la N) := by ring
      _ = _ := by rw [← h2, mul_assoc, h1, mul_one]
  have hv := val_le_one_of_mem X la N hmem
  rw [map_mul, map_inv₀, map_pow, val_algebraMap] at hv
  have hvϖ0 : Valued.v (ϖ : X.Kl la) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
  have hvϖ : Valued.v (ϖ : X.Kl la) < 1 := by
    refine lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ϖ.2) fun h => ?_
    exact hϖ.not_isUnit ((Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers (Valued.v : Valuation (X.Kl la) _))).mpr h)
  have hv2 : la.valuation B.KO c0 ≤ Valued.v (ϖ : X.Kl la) ^ (n + 1) :=
    by simpa using (mul_inv_le_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ hvϖ0))).mp hv
  have hvβ0 : la.valuation B.KO (p.coeff β) ≠ 0 := (Valuation.ne_zero_iff _).mpr hβ
  have h3 : WithZero.log (la.valuation B.KO (p.coeff β)) ≤ WithZero.log (Valued.v (ϖ : X.Kl la) ^ (n + 1)) :=
    (WithZero.log_le_log hvβ0 (pow_ne_zero _ hvϖ0)).mpr ((hle β).trans hv2)
  have h4 : WithZero.log (Valued.v (ϖ : X.Kl la)) < 0 := by
    rw [← WithZero.log_one, WithZero.log_lt_log hvϖ0 one_ne_zero]; exact hvϖ
  rw [WithZero.log_pow] at h3
  have h5 : vAdd la (p.coeff β) ≤ n := by rw [hn]; exact Int.self_le_toNat _
  unfold vAdd at h5
  have h6 : ((n + 1 : ℕ) : ℤ) * WithZero.log (Valued.v (ϖ : X.Kl la)) ≤ ((n + 1 : ℕ) : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  rw [nsmul_eq_mul] at h3
  push_cast at h3 h6
  linarith

end Maps

section FormsV

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

def uV : B.Cusp j ka →+ ↥(Vw X la N ka) where
  toFun F := ⟨emb X la N (X.inc ka F), emb_mem_Vw X la N ka F⟩
  map_zero' := Subtype.ext (by simp only [map_zero]; rfl)
  map_add' F F' := Subtype.ext (by simp only [map_add]; rfl)

theorem coe_uV (F : B.Cusp j ka) : (uV X la N ka F : Rp X la N) = emb X la N (X.inc ka F) := rfl

theorem uV_smul (a : B.KO) (F : B.Cusp j ka) :
    uV X la N ka (a • F) = jF X la N (MvPolynomial.C a) • uV X la N ka F := by
  apply Subtype.ext
  rw [Submodule.coe_smul, coe_uV, coe_uV, map_smul, emb_smul, jF_C,
    algebraMap_smul (Kp X la N) (algebraMap B.KO (X.Kl la) a)]

theorem exists_ext (φ : B.Cusp j ka →ₗ[B.KO] B.KO) :
    ∃ φ1 : ↥(Vw X la N ka) →ₗ[Kp X la N] Kp X la N, ∀ F, φ1 (uV X la N ka F) = jF X la N (MvPolynomial.C (φ F)) := by
  obtain ⟨g, hg⟩ := (X.inc ka).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (X.inc_inj ka))
  let φ' : X.Forms →ₗ[B.KO] X.Kl la := (Algebra.linearMap B.KO (X.Kl la)) ∘ₗ φ ∘ₗ g
  let φ2 : X.Vl la →ₗ[X.Kl la] X.Kl la := (TensorProduct.isBaseChange B.KO X.Forms (X.Kl la)).lift φ'
  let φ3 : Rp X la N →ₗ[Kp X la N] Kp X la N :=
    (bcV_isBaseChange X la N).lift ((Algebra.linearMap (X.Kl la) (Kp X la N)) ∘ₗ φ2)
  refine ⟨φ3 ∘ₗ (Vw X la N ka).subtype, fun F => ?_⟩
  have h2 : φ2 (X.bc la (X.inc ka F)) = algebraMap B.KO (X.Kl la) (φ F) := by
    have := (TensorProduct.isBaseChange B.KO X.Forms (X.Kl la)).lift_eq φ' (X.inc ka F)
    have hgF : g (X.inc ka F) = F := LinearMap.congr_fun hg F
    rw [show φ' (X.inc ka F) = algebraMap B.KO (X.Kl la) (φ (g (X.inc ka F))) from rfl, hgF] at this
    exact this
  have h3 := (bcV_isBaseChange X la N).lift_eq ((Algebra.linearMap (X.Kl la) (Kp X la N)) ∘ₗ φ2) (X.bc la (X.inc ka F))
  rw [LinearMap.comp_apply, h2] at h3
  rw [jF_C]
  exact h3

theorem integralForms_eq_span_image : M1 X la N ka = Submodule.span (Op X la N) (uV X la N ka '' (B.Mlat j ka : Set (B.Cusp j ka))) := by
  apply le_antisymm
  · unfold M1
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have key : ∀ y ∈ X.loc la (X.Msup ka), bcV X la N y ∈
        (Submodule.span (Op X la N) (uV X la N ka '' (B.Mlat j ka : Set (B.Cusp j ka)))).map
          ((Vw X la N ka).subtype.restrictScalars (Op X la N)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨F', ⟨F, hF, rfl⟩, rfl⟩ := hy
        exact ⟨uV X la N ka F, Submodule.subset_span ⟨F, hF, rfl⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
      | smul a y _ hy =>
        rw [← algebraMap_smul (X.Kl la) a y, map_smul, algebraMap_smul, ← algebraMap_smul (Op X la N) a]
        exact Submodule.smul_mem _ _ hy
    obtain ⟨v, hv, hve⟩ := key _ hx
    have : jW X la N ka x = v := Subtype.ext hve.symm
    rw [this]; exact hv
  · rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    refine Submodule.subset_span ⟨toW X la ka ⟨F, hF⟩, ?_, rfl⟩
    exact Submodule.subset_span ⟨X.inc ka F, ⟨F, hF, rfl⟩, rfl⟩

def psi : MvPolynomial (Idx D j N) X.Forms →+* Rp X la N :=
  MvPolynomial.eval₂Hom (emb X la N)
    fun p => algebraMap (Kp X la N) (Rp X la N) (algebraMap (Op X la N) (Kp X la N) (Tv X la N p))

theorem psi_monomial (β : Idx D j N →₀ ℕ) (F : X.Forms) :
    psi X la N (MvPolynomial.monomial β F) = jF X la N (MvPolynomial.monomial β 1) • emb X la N F := by
  rw [Algebra.smul_def]
  simp [psi, jF, jK, MvPolynomial.eval₂_monomial, Finsupp.prod, map_prod, map_pow, mul_comm]

end FormsV

section Word

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL w0 : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem psi_zPoly (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j w0) :
    psi X la N (SizeBoundsAlt.zPoly X w al θ) = secPow X la w al * emb X la N (X.inc w0 θ) := by
  unfold SizeBoundsAlt.zPoly secPow sec psi
  simp only [map_mul, map_prod, map_pow, map_sum, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Algebra.smul_def]

theorem coe_zSum (ka : WeightFamilies.Wt D j) (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j w0)
    (zc : (Idx D j N →₀ ℕ) →₀ B.Cusp j ka) (h : ∀ β, X.inc ka (zc β) = (SizeBoundsAlt.zPoly X w al θ).coeff β) :
    ((∑ β ∈ zc.support, jF X la N (MvPolynomial.monomial β 1) • uV X la N ka (zc β) : ↥(Vw X la N ka)) : Rp X la N) =
      secPow X la w al * emb X la N (X.inc w0 θ) := by
  rw [← psi_zPoly, SizeBoundsAlt.polynomial_eq_sum_monomials (inc := fun w => (X.inc w).toAddMonoidHom) zc h, map_sum,
    AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [psi_monomial, Submodule.coe_smul, coe_uV]
  rfl

end Word

section Main

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ}

theorem iterated_weight_at_vanishingOrder (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (T : ℕ) (hDT : WeightFamilies.dimY D j ≤ T) :
    SizeBoundsAlt.wtIter wadd wL (X.wF0 wL wF) (a0 D j T) = addL wF wL T := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hDT
  have ha : a0 D j (WeightFamilies.dimY D j + a) = a := by unfold a0; omega
  rw [ha]
  apply SizeBoundsAlt.weight_ext
  · funext τ i
    rw [SizeBoundsAlt.weight_iterate_positive_part]
    simp only [PJ.wF0, addL, wadd, wsmul]
    ring
  · funext τ i
    rw [SizeBoundsAlt.weight_iterate_negative_part]
    simp only [PJ.wF0, addL, wadd, wsmul]
    ring
  · rw [SizeBoundsAlt.weight_iterate_n]
    simp only [PJ.wF0, addL, wadd, wsmul]
    ring

theorem len_Zm_le (G : GlobalFamilyData X (addL wF wL T) wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (hfg : (B.Mlat j (addL wF wL T)).FG) (hDT : WeightFamilies.dimY D j ≤ T)
    (hw : ∀ k, G.w k ∈ B.Mlat j wL) (hth0 : ∀ k, G.th0 k ∈ B.Mlat j (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hzc : ∀ k β, X.inc _ (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β)
    (hdet : ∃ φ : Fin G.rz → B.Cusp j (addL wF wL T) →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0) :
    Module.length (Op X la G.N) (↥(Zm G la) ⧸ (Zl G la).comap (Zm G la).subtype) ≤
      (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j (addL wF wL T)) G.zc la : ℕ∞) := by
  obtain ⟨z', hz1, hz2⟩ := SizeBoundsAlt.exists_zFam X (addL wF wL T) wL (X.wF0 wL wF) (a0 D j T) (iterated_weight_at_vanishingOrder X wL wF T hDT)
    G.w hw G.th0 hth0 G.alz hal
  have hz : ∀ k β, G.zc k β ∈ B.Mlat j (addL wF wL T) := fun k β => by
    have : G.zc k β = z' k β := X.inc_inj _ ((hzc k β).trans (hz1 k β).symm)
    rw [this]; exact hz2 k β
  have hZg : Zg G la = Set.range fun k => ∑ β ∈ (G.zc k).support,
      jF X la G.N (MvPolynomial.monomial β 1) • uV X la G.N (addL wF wL T) (G.zc k β) := by
    ext f
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext ((coe_zSum X la G.w _ (G.alz k) (G.th0 k) (G.zc k) (hzc k)).trans hk.symm)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, coe_zSum X la G.w _ (G.alz k) (G.th0 k) (G.zc k) (hzc k)⟩
  have key := SizeBoundsAlt.len_le_gaussC hfg hz hdet la (R := Op X la G.N) (F := Kp X la G.N) (jF X la G.N)
    (jF_C_mem X la G.N) (jF_monomial_mem X la G.N) (addVal_le_vAdd X la G.N) (uV X la G.N (addL wF wL T))
    (uV_smul X la G.N _) (exists_ext X la G.N _) (Zl G la) (by unfold Zl; rw [hZg])
  unfold Zm ZK
  rw [integralForms_eq_span_image, hZg]
  exact key

end Main

end Formalism.MainNotions.Gaps.EtaleWeightGaps

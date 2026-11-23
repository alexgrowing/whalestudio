import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

section
variable {K : Type} [Field K] [NumberField K]

theorem uniformizer_abs_eq_inv_norm (la : HeightOneSpectrum (𝓞 K)) :
    FinitePlace.mk la ((Data.unif la : 𝓞 K) : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨h1, h2⟩ := unif_mem la
  have a1 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((la.intValuation_le_pow_iff_mem _ 2).1 h)
  have hne : la.intValuation (Data.unif la) ≠ 0 := by
    intro h0; apply a2; rw [h0]; exact zero_le
  have hv : la.intValuation (Data.unif la) = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hne] at a1 a2 ⊢
    rw [WithZero.exp_le_exp] at a1 a2
    congr 1
    push_cast at a1 a2
    omega
  rw [FinitePlace.mk_apply]
  have := FinitePlace.norm_embedding_int (K := K) (v := la) (Data.unif la)
  simp only [RingOfIntegers.coe_eq_algebraMap] at this ⊢
  rw [this, hv]
  simp [WithZeroMulInt.toNNReal_neg_apply, WithZero.exp]

theorem logHeight_div_multihomogeneous {B n : ℕ} {P Q R : MvPolynomial (Fin B × Fin n) K}
    (eQ eR : Fin B → ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hQm : IsMultiHomogeneous eQ Q)
    (hRm : IsMultiHomogeneous eR R) (hPQ : P * Q = R) :
    h0 P = h0 R - h0 Q := by
  have hR : R ≠ 0 := hPQ ▸ mul_ne_zero hP hQ
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w P) =
      (∑ᶠ w : FinitePlace K, Real.log (gaussAbs w R)) - ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w Q) := by
    rw [← finsum_sub_distrib (gauss_abs_log_support_finite R hR) (gauss_abs_log_support_finite Q hQ)]
    refine finsum_congr fun w => ?_
    rw [← hPQ, gauss_abs_mul w P Q hP hQ,
      Real.log_mul (gauss_abs_pos_of_ne_zero w P hP).ne' (gauss_abs_pos_of_ne_zero w Q hQ).ne']
    ring
  have harch : ∀ σ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map σ P) =
      blockSphereMean B n (MvPolynomial.map σ R) - blockSphereMean B n (MvPolynomial.map σ Q) := by
    intro σ
    have hs : ∀ F : MvPolynomial (Fin B × Fin n) K, F ≠ 0 → MvPolynomial.map σ F ≠ 0 := by
      intro F hF h'
      exact hF (MvPolynomial.map_injective σ σ.injective (by rw [h', map_zero]))
    have IR := sphereLogIntegrable B n eR _ (hs R hR) (isMultiHomogeneous_map_ring eR R hRm σ)
    have IQ := sphereLogIntegrable B n eQ _ (hs Q hQ) (isMultiHomogeneous_map_ring eQ Q hQm σ)
    have aR := ae_blockSphere_eval_ne_zero B n eR _ (hs R hR) (isMultiHomogeneous_map_ring eR R hRm σ)
    have aQ := ae_blockSphere_eval_ne_zero B n eQ _ (hs Q hQ) (isMultiHomogeneous_map_ring eQ Q hQm σ)
    unfold blockSphereMean
    rw [← integral_sub IR IQ]
    refine integral_congr_ae ?_
    filter_upwards [aR, aQ] with z hzR hzQ
    have hRe : MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ R) =
        MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ P) *
          MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ Q) := by
      rw [← hPQ, map_mul, map_mul]
    have hzP : MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ P) ≠ 0 := by
      intro h0; apply hzR; rw [hRe, h0, zero_mul]
    rw [hRe, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hzP) (norm_ne_zero_iff.2 hzQ)]
    ring
  unfold h0
  rw [hfin, Finset.sum_congr rfl fun σ _ => harch σ, Finset.sum_sub_distrib]
  ring

end

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

namespace Data

variable (d : Data K ι Ω WT A)

theorem log_gaussAbs_sub_of_fraction (la : HeightOneSpectrum (𝓞 K)) (a b : KTp K d.D d.N) (ha : a ≠ 0) (hb : b ≠ 0)
    (q : KTf K d.D d.N)
    (hq : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a = q * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b) :
    Real.log (gaussAbs (FinitePlace.mk la) a) - Real.log (gaussAbs (FinitePlace.mk la) b) =
      -((d.gOrd la q : ℝ) * logNorm la) := by
  classical
  let _ := algOpKT (K := K) d.D d.N la
  have := isFractionRing_Op (K := K) d.D d.N la
  have := Op_isDVR (K := K) d.D d.N la
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [zero_mul] at hq; exact ha (hinj (by rw [hq, map_zero]))
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := Op d.D d.N la) q
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hq0
  obtain ⟨n1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0
    (unifOp_irreducible d.D d.N la)
  obtain ⟨n2, u2, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0
    (unifOp_irreducible d.D d.N la)
  set π := algebraMap K (KTf K d.D d.N) ((Data.unif la : 𝓞 K) : K) with hπdef
  have hπ : OpToKT d.D d.N la (unifOp d.D d.N la) = π := (algK_unif d.D d.N la).symm
  have hπ0 : π ≠ 0 := by
    rw [← hπ]
    exact (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr (unifOp_irreducible d.D d.N la).ne_zero
  have hE : ∀ z : Op d.D d.N la, algebraMap (Op d.D d.N la) (KTf K d.D d.N) z = OpToKT d.D d.N la z :=
    fun _ => rfl
  have hU : ∀ u : (Op d.D d.N la)ˣ, OpToKT d.D d.N la (u : Op d.D d.N la) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr u.ne_zero

  have hg : d.gOrd la (algebraMap (Op d.D d.N la) (KTf K d.D d.N) (↑u1 * unifOp d.D d.N la ^ n1) /
      algebraMap (Op d.D d.N la) (KTf K d.D d.N) (↑u2 * unifOp d.D d.N la ^ n2)) = (n1 : ℤ) - n2 := by
    refine d.gOrd_eq la (u := ((u1 * u2⁻¹ : (Op d.D d.N la)ˣ) : Op d.D d.N la)) (Units.isUnit _) ?_
    rw [hE, hE, map_mul, map_mul, map_pow, map_pow, hπ, Units.val_mul, map_mul,
      map_units_inv (OpToKT d.D d.N la) u2, zpow_sub₀ hπ0, zpow_natCast, zpow_natCast]
    have := hU u2
    field_simp
  rw [hg]

  obtain ⟨⟨x1, s1⟩, hu1⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl (u1 : Op d.D d.N la)
  obtain ⟨⟨x2, s2⟩, hu2⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl (u2 : Op d.D d.N la)
  dsimp only at hu1 hu2
  have hx1 : x1 ∈ (laT d.D d.N la).primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (Op d.D d.N la) (laT d.D d.N la) x1 s1).1 (hu1 ▸ u1.isUnit)
  have hx2 : x2 ∈ (laT d.D d.N la).primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (Op d.D d.N la) (laT d.D d.N la) x2 s2).1 (hu2 ▸ u2.isUnit)
  set g := (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)).comp (OTtoKT K d.D d.N) with hgdef
  have hs1 : g x1 = g s1 * OpToKT d.D d.N la (u1 : Op d.D d.N la) := by
    rw [← hu1]; exact (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
  have hs2 : g x2 = g s2 * OpToKT d.D d.N la (u2 : Op d.D d.N la) := by
    rw [← hu2]; exact (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
  have hX : x2 * (s1 : OT K d.D d.N) ∈ (laT d.D d.N la).primeCompl :=
    (laT d.D d.N la).primeCompl.mul_mem hx2 s1.2
  have hY : x1 * (s2 : OT K d.D d.N) ∈ (laT d.D d.N la).primeCompl :=
    (laT d.D d.N la).primeCompl.mul_mem hx1 s2.2
  have hπC : π = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (C ((Data.unif la : 𝓞 K) : K)) := by
    rw [hπdef, IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N), MvPolynomial.algebraMap_eq]

  have hpoly : a * OTtoKT K d.D d.N (x2 * (s1 : OT K d.D d.N)) * C (((Data.unif la : 𝓞 K) : K) ^ n2) =
      C (((Data.unif la : 𝓞 K) : K) ^ n1) * OTtoKT K d.D d.N (x1 * (s2 : OT K d.D d.N)) * b := by
    apply hinj
    have hs1' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N x1) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N (s1 : OT K d.D d.N)) *
          OpToKT d.D d.N la (u1 : Op d.D d.N la) := hs1
    have hs2' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N x2) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (OTtoKT K d.D d.N (s2 : OT K d.D d.N)) *
          OpToKT d.D d.N la (u2 : Op d.D d.N la) := hs2
    have e3 : ∀ m : ℕ, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (C (((Data.unif la : 𝓞 K) : K) ^ m)) = π ^ m := by
      intro m; rw [hπC, MvPolynomial.C_pow, map_pow]
    simp only [map_mul, e3]
    rw [hq, hs1', hs2']
    simp only [hE, map_mul, map_pow, hπ]
    have := hU u2
    have := hπ0
    field_simp

  set w := FinitePlace.mk la
  have hXn : gaussAbs w (OTtoKT K d.D d.N (x2 * (s1 : OT K d.D d.N))) = 1 := gaussAbs_prim la _ hX
  have hYn : gaussAbs w (OTtoKT K d.D d.N (x1 * (s2 : OT K d.D d.N))) = 1 := gaussAbs_prim la _ hY
  have hX0 : OTtoKT K d.D d.N (x2 * (s1 : OT K d.D d.N)) ≠ 0 := by intro h0; rw [h0] at hXn; simp [gaussAbs] at hXn
  have hY0 : OTtoKT K d.D d.N (x1 * (s2 : OT K d.D d.N)) ≠ 0 := by intro h0; rw [h0] at hYn; simp [gaussAbs] at hYn
  have hN : (0 : ℝ) < ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact_mod_cast (zero_lt_one.trans this)
  have hϖ0 : ((Data.unif la : 𝓞 K) : K) ≠ 0 := by
    intro h0; have := uniformizer_abs_eq_inv_norm la; rw [h0, map_zero] at this; exact (inv_pos.2 hN).ne' this.symm
  have hC0 : ∀ m : ℕ, (C (((Data.unif la : 𝓞 K) : K) ^ m) : KTp K d.D d.N) ≠ 0 := fun m => by
    rw [Ne, C_eq_zero]; exact pow_ne_zero _ hϖ0
  have key := congrArg (gaussAbs w) hpoly
  rw [gauss_abs_mul w _ _ (mul_ne_zero ha hX0) (hC0 n2), gauss_abs_mul w _ _ ha hX0,
    gauss_abs_mul w _ _ (mul_ne_zero (hC0 n1) hY0) hb, gauss_abs_mul w _ _ (hC0 n1) hY0,
    gaussAbs_C, gaussAbs_C, map_pow, map_pow, uniformizer_abs_eq_inv_norm la, hXn, hYn, mul_one, mul_one] at key
  have hA' := gauss_abs_pos_of_ne_zero w a ha
  have hB' := gauss_abs_pos_of_ne_zero w b hb
  have hlogN : logNorm la = Real.log ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := rfl
  have hl := congrArg Real.log key
  rw [Real.log_mul hA'.ne' (pow_ne_zero _ (inv_pos.2 hN).ne'),
    Real.log_mul (pow_ne_zero _ (inv_pos.2 hN).ne') hB'.ne', Real.log_pow, Real.log_pow, Real.log_inv] at hl
  rw [hlogN]
  push_cast
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0

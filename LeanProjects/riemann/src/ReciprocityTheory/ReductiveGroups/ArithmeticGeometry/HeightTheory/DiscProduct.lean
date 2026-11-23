import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteHeightFractionRepr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDC

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_product (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (Om : KTp K d.D d.N)
    (hOm : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
        (Module.finrank ℚ K : ℝ) =
      meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) -
        ReciprocityTheory.MultiplicativeHeights.h0 Om + 2 * d.Hgt h d.wF hd.a4.choose := by
  classical
  set e := hd.a4.choose with hedef
  have he := hd.a4.choose_spec.1
  obtain ⟨hb0, hab', m, hm0, hma, hmb⟩ := hab
  have hDe : d.De hd h ≠ 0 := (d.disc_lattice hd h).1
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab'
    exact mul_ne_zero hDe ((map_ne_zero_iff _ hinj).2 hb0) hab'.symm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ

  have hla : ∀ la, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) =
        -((d.gOrd la (d.De hd h) : ℝ) * logNorm la) :=
    fun la => d.log_gaussAbs_sub_of_fraction la a b ha0 hb0 _ hab'
  have hlog : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), logNorm la ≠ 0 := fun la => by
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact (Real.log_pos (by exact_mod_cast h1)).ne'
  have hgfin : (Function.support fun la => d.gOrd la (d.De hd h)).Finite := by
    refine (((ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0).union
      (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn).subset ?_
    intro la hla0
    have h1 : Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
        Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) ≠ 0 := by
      rw [hla]
      exact neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hla0) (hlog la))
    by_contra hn'
    apply h1
    simp only [Set.mem_preimage, Set.mem_union, Function.mem_support, not_or, not_not] at hn'
    change Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) = 0 ∧
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) = 0 at hn'
    rw [hn'.1, hn'.2, sub_zero]
  have hNfin : (Function.support fun la => d.NlaG h d.wF e la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v d.wF (e c))
      (hd.a3' c (he c).1 (he c).2)).subset (d.aNla_supp hd h (fun c v f => d.ord c v d.wF f) e)
  refine ⟨hgfin, hNfin, ?_⟩

  obtain ⟨U, V, hU0, hV0, ⟨eU, hUm⟩, ⟨eV, hVm⟩, hpres, hh0f⟩ := d.finite_height_fraction_repr hd h
  have hpoly : Om * (b * V ^ 2) = a * U ^ 2 := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [hOm, omE, hab', ← hpres]
    ring
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hpoly
    exact mul_ne_zero ha0 (pow_ne_zero _ hU0) hpoly.symm
  have hnp : 0 < d.N + 1 := Nat.succ_pos _
  have E1 : ReciprocityTheory.MultiplicativeHeights.h0 Om = ReciprocityTheory.MultiplicativeHeights.h0 a + 2 * ReciprocityTheory.MultiplicativeHeights.h0 U -
      (ReciprocityTheory.MultiplicativeHeights.h0 b + 2 * ReciprocityTheory.MultiplicativeHeights.h0 V) := by
    rw [logHeight_div_multihomogeneous _ _ hOm0 (mul_ne_zero hb0 (pow_ne_zero _ hV0))
      (multi_mul hmb (multi_pow hVm 2)) (multi_mul hma (multi_pow hUm 2)) hpoly,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ a (U ^ 2) hnp ha0 (pow_ne_zero _ hU0) hma
        (multi_pow hUm 2)).1,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ b (V ^ 2) hnp hb0 (pow_ne_zero _ hV0) hmb
        (multi_pow hVm 2)).1,
      h0_pow_of_isMultiHomogeneous hnp hU0 hUm, h0_pow_of_isMultiHomogeneous hnp hV0 hVm]
    push_cast; ring
  have E2 : ReciprocityTheory.MultiplicativeHeights.h0 a - ReciprocityTheory.MultiplicativeHeights.h0 b =
      (-(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) + ∑ sg, d.mSgP sg a b) /
        (Module.finrank ℚ K : ℝ) := by
    have hfinp : (∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a)) -
        ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b) =
        -(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) := by
      rw [← finsum_sub_distrib (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0)
        (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)]
      have := finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
        (f := fun w => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a) - Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b))
      rw [← this, ← finsum_neg_distrib]
      exact finsum_congr fun la => hla la
    have harch : ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
        ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) =
        ∑ sg, d.mSgP sg a b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun sg _ => d.sphereMean_sub_archimedean a b m hm0 ha0 hb0 hma hmb sg
    unfold ReciprocityTheory.MultiplicativeHeights.h0
    rw [← hfinp, ← harch]
    ring
  have E4 : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF e sg) =
      (∑ sg, d.mSgP sg a b) / (Module.finrank ℚ K : ℝ) - 2 * meanK (d.Nsg d.wF e) := by
    unfold meanK
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcard]
    ring
  have hsG : (Function.support fun la => (d.gOrd la (d.De hd h) : ℝ) * logNorm la).Finite :=
    hgfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have hsN : (Function.support fun la => d.NlaG h d.wF e la * logNorm la).Finite :=
    hNfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have E5 : (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF e la) * logNorm la) =
      (∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) +
        2 * ∑ᶠ la, d.NlaG h d.wF e la * logNorm la := by
    rw [mul_finsum, ← finsum_add_distrib hsG (hsN.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0])]
    exact finsum_congr fun la => by ring
  rw [E5, E4, Hgt, hh0f]
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := hn.ne'
  linear_combination E1 + E2

end Data

end ReciprocityTheory.ChartRestriction.G.T0

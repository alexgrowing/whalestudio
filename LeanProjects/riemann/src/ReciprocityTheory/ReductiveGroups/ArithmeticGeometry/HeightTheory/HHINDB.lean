import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def lsum (c : ι) (sg : K →+* ℂ) (a : Ω c) (z : BlockSphere d.D (d.N + 1)) : ℝ :=
  ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log ‖P a‖

theorem blockPoint_eq_evT (sg : K →+* ℂ) (z : BlockSphere (d.D + 1) (d.N + 1)) (q : KTp K d.D d.N) :
    eval (blockPoint z) (MvPolynomial.map sg q) =
      d.evT sg (spherePoint (z 0)) (d.tOf ((ReciprocityTheory.MultiplicativeHeights.lh0Split d.D (d.N + 1) z).2)) q := by
  rw [MvPolynomial.eval_map]
  unfold Data.evT
  congr 1
  funext v
  obtain ⟨i, j⟩ := v
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    show spherePoint (z i.succ) j = spherePoint (z (Fin.succAbove 0 i)) j
    rw [Fin.succAbove_zero]

theorem pf_arch (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (a : Ω c) (ha : a ≠ 0)
    (PA PB : KTp K d.D d.N) (hA : PA ≠ 0) (hB : PB ≠ 0) (eA eB : Fin (d.D + 1) → ℕ)
    (hAm : IsMultiHomogeneous eA PA) (hBm : IsMultiHomogeneous eB PB)
    (hAB : letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PB =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PA)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PA) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PB) =
      ∫ z, d.lsum c sg a z ∂(blockSphereProb d.D (d.N + 1)) := by
  have hP1 := sphereMeasure_isProbability (n := d.N + 1) (Nat.succ_pos _)
  have hPD := blockSphereMeasure_isProbability (B := d.D) (n := d.N + 1) (Nat.succ_pos _)
  have hSF : SFinite (blockSphereProb d.D (d.N + 1)) := by have := hPD; infer_instance
  have hSF1 : SFinite (sphereProb (d.N + 1)) := by have := hP1; infer_instance
  set e := ReciprocityTheory.MultiplicativeHeights.lh0Split d.D (d.N + 1)
  have hmp : MeasurePreserving e.symm ((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1)))
      (blockSphereProb (d.D + 1) (d.N + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => sphereProb (d.N + 1)) 0).symm _
  have hmp' : MeasurePreserving e (blockSphereProb (d.D + 1) (d.N + 1))
      ((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1))) :=
    measurePreserving_piFinSuccAbove (fun _ => sphereProb (d.N + 1)) 0
  have hsnd : MeasurePreserving (fun z => (e z).2) (blockSphereProb (d.D + 1) (d.N + 1))
      (blockSphereProb d.D (d.N + 1)) :=
    (measurePreserving_snd (μ := sphereProb (d.N + 1)) (ν := blockSphereProb d.D (d.N + 1))).comp hmp'
  have hsA : MvPolynomial.map sg PA ≠ 0 := by
    rw [Ne, ← map_zero (MvPolynomial.map sg)]; exact fun h' => hA (MvPolynomial.map_injective sg sg.injective h')
  have hsB : MvPolynomial.map sg PB ≠ 0 := by
    rw [Ne, ← map_zero (MvPolynomial.map sg)]; exact fun h' => hB (MvPolynomial.map_injective sg sg.injective h')
  have hIA := sphereLogIntegrable (d.D + 1) (d.N + 1) eA _ hsA (isMultiHomogeneous_map_ring eA PA hAm sg)
  have hIB := sphereLogIntegrable (d.D + 1) (d.N + 1) eB _ hsB (isMultiHomogeneous_map_ring eB PB hBm sg)
  have hB0 := ae_blockSphere_eval_ne_zero (d.D + 1) (d.N + 1) eB _ hsB (isMultiHomogeneous_map_ring eB PB hBm sg)
  have hS := hsnd.quasiMeasurePreserving.ae (d.norm_at_sg hd h c sg)
  have hae : (fun z => Real.log ‖eval (blockPoint z) (MvPolynomial.map sg PA)‖ -
      Real.log ‖eval (blockPoint z) (MvPolynomial.map sg PB)‖) =ᵐ[blockSphereProb (d.D + 1) (d.N + 1)]
      fun z => d.lsum c sg a (e z).2 := by
    filter_upwards [hB0, hS] with z hz0 hz
    beta_reduce at hz
    obtain ⟨hfin, -, hrat, -⟩ := hz
    rw [d.blockPoint_eq_evT] at hz0 ⊢
    rw [d.blockPoint_eq_evT]
    have hfin : (d.ST c sg (d.tOf (e z).2)).Finite := hfin
    have hz0 : d.evT sg (spherePoint (z 0)) (d.tOf (e z).2) PB ≠ 0 := hz0
    have hr := hrat a PA PB (spherePoint (z 0)) ha hB hAB hz0
    have hprod : ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf (e z).2)), P a =
        ∏ P ∈ hfin.toFinset, P a := by
      rw [finprod_mem_eq_finite_toFinset_prod (fun P : Ω c →+* ℂ => P a) hfin]
    have hne : ∀ P ∈ hfin.toFinset, P a ≠ 0 := fun P _ => (map_ne_zero P).2 ha
    have hpne : ∏ P ∈ hfin.toFinset, P a ≠ 0 := Finset.prod_ne_zero_iff.2 hne
    rw [hprod] at hr
    have hAe : d.evT sg (spherePoint (z 0)) (d.tOf (e z).2) PA =
        d.evT sg (spherePoint (z 0)) (d.tOf (e z).2) PB * ∏ P ∈ hfin.toFinset, P a := by
      rw [← hr]; field_simp
    unfold lsum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, hAe, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hz0)
      (norm_ne_zero_iff.2 hpne), norm_prod, Real.log_prod (fun P hP => norm_ne_zero_iff.2 (hne P hP))]
    ring
  unfold blockSphereMean
  rw [← integral_sub hIA hIB, integral_congr_ae hae]
  have h2 : ∫ z, d.lsum c sg a (e z).2 ∂(blockSphereProb (d.D + 1) (d.N + 1)) =
      ∫ p, d.lsum c sg a p.2 ∂((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1))) := by
    rw [← hmp.integral_comp' (fun z => d.lsum c sg a (e z).2)]
    simp
  rw [h2, integral_fun_snd]
  simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def nPa (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (a : Ω c) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a)

theorem Wres_apply (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (a : Ω c) :
    d.Wres c w a = w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) := rfl

theorem nPa_support (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (a : Ω c) (ha : a ≠ 0) :
    {p | p ∈ d.HtOne ∧ d.nPa h c p a ≠ 0}.Finite := by
  have hy : algebraMap (Ω c) (OmS (Ω c) d.D d.N) a ≠ 0 :=
    (map_ne_zero (algebraMap (Ω c) (OmS (Ω c) d.D d.N))).2 ha
  refine ((d.norm_by_places hd h c).2 _ hy).1.subset ?_
  rintro p ⟨hp, hn⟩
  refine ⟨hp, ?_⟩
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finsum_mem_ne_zero hn
  refine ⟨w, hw.1, fun h0 => hw0 ?_⟩
  rw [d.Wres_apply, h0]; simp

theorem good_of_nPa (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (a : Ω c)
    (hn : d.nPa h c p a ≠ 0) : ∃ w, w ∈ d.GoodP c p := by
  by_contra hc
  push_neg at hc
  apply hn
  simp [nPa, hc]

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem pf (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (a : Ω c) (ha : a ≠ 0) :
    (∑ᶠ la, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a) : ℝ) * logNorm la) /
        (Module.finrank ℚ K : ℝ) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nPa h c p a : ℝ) * h0 (d.gen p) =
      meanK (fun sg => ∫ z, d.lsum c sg a z ∂(blockSphereProb d.D (d.N + 1))) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  set y := algebraMap (Ω c) (OmS (Ω c) d.D d.N) a with hydef
  have hy : y ≠ 0 := (map_ne_zero _).2 ha
  obtain ⟨κ, hκ, hN⟩ := (d.norm_factorization hd h).1 c a ha
  have hSfin := d.nPa_support hd h c a ha
  set T := hSfin.toFinset with hTdef
  set n : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPa h c p a with hndef
  set g : Ideal (KTp K d.D d.N) → KTf K d.D d.N :=
    fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hgdef
  have hN' : Algebra.norm (KTf K d.D d.N) y =
      algebraMap K (KTf K d.D d.N) κ * ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ (n p) := hN
  have hTmem : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hprod : ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ (n p) = ∏ p ∈ T, g p ^ (n p) := by
    apply finprod_cond_eq_prod_of_cond_iff
    intro p hp
    rw [hTmem]
    constructor
    · intro h1; exact ⟨h1, fun h0' => hp (by rw [h0', zpow_zero])⟩
    · exact fun h1 => h1.1
  have hNm0 : Algebra.norm (KTf K d.D d.N) y ≠ 0 := by
    by_cases hfin : Module.Finite (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
    · exact Algebra.norm_ne_zero_iff.2 hy
    · rw [Algebra.norm_eq_one_of_not_module_finite hfin]; exact one_ne_zero
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hgen : ∀ p ∈ T, d.gen p ≠ 0 := by
    intro p hp h0'
    apply hNm0
    rw [hN', hprod, Finset.prod_eq_zero hp (by
      simp only [g, h0', map_zero]; exact zero_zpow _ ((hTmem p).1 hp).2), mul_zero]
  set e : Ideal (KTp K d.D d.N) → Fin (d.D + 1) → ℕ :=
    fun p b => if b = 0 then 0 else d.dg (d.gen p) with hedef
  have hmh : ∀ p ∈ T, IsMultiHomogeneous (e p) (d.gen p) := fun p hp =>
    (d.good_primes_properties hd h c).2.1 p ((hTmem p).1 hp).1 (d.good_of_nPa h c p a ((hTmem p).1 hp).2)
  set PA' : KTp K d.D d.N := ∏ p ∈ T, d.gen p ^ (n p).toNat with hPA'def
  set PA : KTp K d.D d.N := C κ * PA' with hPAdef
  set PB : KTp K d.D d.N := ∏ p ∈ T, d.gen p ^ (-n p).toNat with hPBdef
  have hPA0' : PA' ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hgen p hp)
  have hPA0 : PA ≠ 0 := mul_ne_zero (by rw [Ne, C_eq_zero]; exact hκ) hPA0'
  have hPB0 : PB ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hgen p hp)
  have hPAm' := multi_prod T (fun p => (n p).toNat • e p) (fun p => d.gen p ^ (n p).toNat)
    (fun p hp => multi_pow (hmh p hp) _)
  have hPAm := multi_mul (multi_C κ) hPAm'
  have hPBm := multi_prod T (fun p => (-n p).toNat • e p) (fun p => d.gen p ^ (-n p).toNat)
    (fun p hp => multi_pow (hmh p hp) _)
  have hAB : Algebra.norm (KTf K d.D d.N) y * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PB =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PA := by
    rw [hN', hprod, d.algK_eq, hPAdef, hPBdef, hPA'def]
    simp only [map_mul, map_prod, map_pow]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hg0 : g p ≠ 0 := fun h0' => hgen p hp (hinj (by rw [map_zero]; exact h0'))
    show g p ^ n p * g p ^ (-n p).toNat = g p ^ (n p).toNat
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hg0]
    congr 1; omega
  have hh0 : h0 PA - h0 PB = ∑ p ∈ T, (n p : ℝ) * h0 (d.gen p) := by
    have h1 : h0 PA = h0 PA' :=
      (gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ PA' PA' (Nat.succ_pos _) hPA0' hPA0' hPAm' hPAm').2 κ hκ
    rw [h1, hPA'def, hPBdef, logHeight_prod_pow (Nat.succ_pos _) T e d.gen (fun p => (n p).toNat) hgen hmh,
      logHeight_prod_pow (Nat.succ_pos _) T e d.gen (fun p => (-n p).toNat) hgen hmh,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    have : ((n p).toNat : ℝ) - ((-n p).toNat : ℝ) = n p := by
      have := Int.toNat_sub_toNat_neg (n p)
      exact_mod_cast this
    rw [← sub_mul, this]
  have hsum : ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nPa h c p a : ℝ) * h0 (d.gen p) =
      ∑ p ∈ T, (n p : ℝ) * h0 (d.gen p) := by
    apply finsum_cond_eq_sum_of_cond_iff
    intro p hp
    rw [hTmem]
    constructor
    · intro h1; exact ⟨h1, fun h0' => hp (by simp [hndef] at h0' ⊢; simp [h0'])⟩
    · exact fun h1 => h1.1
  have hsplit : h0 PA - h0 PB = ((∑ᶠ w : FinitePlace K,
      (Real.log (gaussAbs w PA) - Real.log (gaussAbs w PB))) +
      ∑ sg : K →+* ℂ, (blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PA) -
        blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PB))) /
        (Module.finrank ℚ K : ℝ) := by
    unfold h0
    rw [finsum_sub_distrib (gauss_abs_log_support_finite PA hPA0) (gauss_abs_log_support_finite PB hPB0),
      Finset.sum_sub_distrib]
    ring
  have hfinp : ∑ᶠ w : FinitePlace K, (Real.log (gaussAbs w PA) - Real.log (gaussAbs w PB)) =
      -∑ᶠ la, (d.nLa h c la y : ℝ) * logNorm la := by
    have := finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
      (f := fun w => Real.log (gaussAbs w PA) - Real.log (gaussAbs w PB))
    rw [← this, ← finsum_neg_distrib]
    apply finsum_congr
    intro la
    exact d.pf_fin hd h c y hy PA PB hPA0 hPB0 hAB la
  have harch : ∑ sg : K →+* ℂ, (blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PA) -
        blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg PB)) =
      ∑ sg : K →+* ℂ, ∫ z, d.lsum c sg a z ∂(blockSphereProb d.D (d.N + 1)) :=
    Finset.sum_congr rfl fun sg _ => d.pf_arch hd h c a ha PA PB hPA0 hPB0 _ _ hPAm hPBm hAB sg
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ
  have hdeg : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold meanK
  rw [hsum, ← hh0, hsplit, hfinp, harch, hcard]
  field_simp
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0

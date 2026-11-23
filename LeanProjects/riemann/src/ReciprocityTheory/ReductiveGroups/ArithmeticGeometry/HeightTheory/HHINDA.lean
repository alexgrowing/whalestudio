import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts

namespace ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

open MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

theorem multi_mul {R : Type*} [CommSemiring R] {B n : ℕ} {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f)
    (hg : IsMultiHomogeneous a' g) : IsMultiHomogeneous (a + a') (f * g) := by
  classical
  intro s hs b
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf s1 hs1 b, hg s2 hs2 b, Pi.add_apply]

theorem multi_one {R : Type*} [CommSemiring R] {B n : ℕ} :
    IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem multi_C {R : Type*} [CommSemiring R] {B n : ℕ} (c : R) :
    IsMultiHomogeneous (0 : Fin B → ℕ) (C c : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem multi_pow {R : Type*} [CommSemiring R] {B n : ℕ} {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f) (k : ℕ) :
    IsMultiHomogeneous (k • a) (f ^ k) := by
  induction k with
  | zero => simpa using (multi_one : IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R))
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact multi_mul ih hf

theorem multi_prod {R : Type*} [CommSemiring R] {B n : ℕ} {α : Type*} (s : Finset α)
    (e : α → Fin B → ℕ) (f : α → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ s, IsMultiHomogeneous (e i) (f i)) :
    IsMultiHomogeneous (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (multi_one : IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact multi_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable {K : Type} [Field K] [NumberField K]

theorem h0_pow_of_isMultiHomogeneous {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) K}
    (hf0 : f ≠ 0) (hf : IsMultiHomogeneous a f) (k : ℕ) : h0 (f ^ k) = k * h0 f := by
  have h1 : h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
    have e := (gauss_height_additivity K B n 0 0 1 1 hn one_ne_zero one_ne_zero multi_one multi_one).1
    rw [one_mul] at e
    linarith
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, (gauss_height_additivity K B n _ a (f ^ k) f hn (pow_ne_zero _ hf0) hf0 (multi_pow hf k) hf).1, ih]
    push_cast
    ring

theorem logHeight_prod_pow {B n : ℕ} (hn : 0 < n) {α : Type*} (s : Finset α) (e : α → Fin B → ℕ)
    (f : α → MvPolynomial (Fin B × Fin n) K) (k : α → ℕ)
    (hf0 : ∀ i ∈ s, f i ≠ 0) (hf : ∀ i ∈ s, IsMultiHomogeneous (e i) (f i)) :
    h0 (∏ i ∈ s, f i ^ k i) = ∑ i ∈ s, (k i : ℝ) * h0 (f i) := by
  classical
  have h1 : h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
    have e := (gauss_height_additivity K B n 0 0 1 1 hn one_ne_zero one_ne_zero multi_one multi_one).1
    rw [one_mul] at e
    linarith
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | insert i s hi ih =>
    have hf0' : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf0 j (Finset.mem_insert_of_mem hj)
    have hf' : ∀ j ∈ s, IsMultiHomogeneous (e j) (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hP0 : ∏ j ∈ s, f j ^ k j ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hf0' j hj)
    have hPm : IsMultiHomogeneous (∑ j ∈ s, k j • e j) (∏ j ∈ s, f j ^ k j) :=
      multi_prod s (fun j => k j • e j) (fun j => f j ^ k j) fun j hj => multi_pow (hf' j hj) (k j)
    have hi0 := hf0 i (Finset.mem_insert_self i s)
    have him := hf i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      (gauss_height_additivity K B n _ _ _ _ hn (pow_ne_zero _ hi0) hP0 (multi_pow him (k i)) hPm).1,
      h0_pow_of_isMultiHomogeneous hn hi0 him, ih hf0' hf']

theorem gaussAbs_C (w : NumberField.FinitePlace K) {σ : Type*} (c : K) :
    gaussAbs w (C c : MvPolynomial σ K) = w c := by
  classical
  unfold gaussAbs
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [MvPolynomial.support_C, if_neg hc]
    simp only [Finset.sup_singleton, MvPolynomial.coeff_C, if_true]
    exact Real.coe_toNNReal _ (by positivity)

end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

namespace ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

open MvPolynomial ReciprocityTheory.MultiplicativeHeights NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

theorem exists_unif (la : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 ∧
      FinitePlace.mk la (ϖ : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  refine ⟨π, ?_, ?_, ?_⟩
  · have h1 := (la.intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    simpa using h1
  · intro h2
    have h3 := (la.intValuation_le_pow_iff_mem π 2).2 h2
    rw [hπ, WithZero.exp_le_exp] at h3
    norm_num at h3
  · rw [FinitePlace.mk_apply, show (π : K) = algebraMap (𝓞 K) K π from rfl, FinitePlace.norm_def_int K la π, hπ,
      WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
    push_cast
    exact zpow_neg_one _

theorem gaussAbs_prim {σ : Type*} (la : HeightOneSpectrum (𝓞 K)) (x : MvPolynomial σ (𝓞 K))
    (hx : x ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal) :
    gaussAbs (FinitePlace.mk la) (MvPolynomial.map (algebraMap (𝓞 K) K) x) = 1 := by
  classical
  rw [MvPolynomial.mem_map_C_iff] at hx
  push_neg at hx
  obtain ⟨s0, hs0⟩ := hx
  have hw : ∀ a : 𝓞 K, FinitePlace.mk la (algebraMap (𝓞 K) K a) ≤ 1 := fun a => by
    rw [FinitePlace.mk_apply]
    exact FinitePlace.norm_le_one K la a
  have hw1 : FinitePlace.mk la (algebraMap (𝓞 K) K (x.coeff s0)) = 1 := by
    rw [FinitePlace.mk_apply]
    exact (FinitePlace.norm_eq_one_iff_notMem K la _).2 hs0
  have hmem : s0 ∈ (MvPolynomial.map (algebraMap (𝓞 K) K) x).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
    intro h0
    rw [h0, map_zero] at hw1
    exact zero_ne_one hw1
  unfold gaussAbs
  apply le_antisymm
  · have h1 : ((MvPolynomial.map (algebraMap (𝓞 K) K) x).support.sup fun s =>
        (FinitePlace.mk la ((MvPolynomial.map (algebraMap (𝓞 K) K) x).coeff s)).toNNReal) ≤ 1 := by
      apply Finset.sup_le
      intro s _
      rw [MvPolynomial.coeff_map]
      exact Real.toNNReal_le_one.2 (hw _)
    exact_mod_cast h1
  · have h1 : (1 : NNReal) ≤ ((MvPolynomial.map (algebraMap (𝓞 K) K) x).support.sup fun s =>
        (FinitePlace.mk la ((MvPolynomial.map (algebraMap (𝓞 K) K) x).coeff s)).toNNReal) := by
      refine Finset.le_sup_of_le hmem ?_
      rw [MvPolynomial.coeff_map, hw1, Real.toNNReal_one]
    exact_mod_cast h1

theorem log_gauss_ratio {σ : Type*} [Fintype σ] (la : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K)
    (hϖ : FinitePlace.mk la (ϖ : K) = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹)
    (A B : MvPolynomial σ K) (hA : A ≠ 0) (hB : B ≠ 0) (X S : MvPolynomial σ (𝓞 K))
    (hX : X ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal)
    (hS : S ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal) (m : ℕ)
    (h : A * MvPolynomial.map (algebraMap (𝓞 K) K) S =
      C ((ϖ : K) ^ m) * MvPolynomial.map (algebraMap (𝓞 K) K) X * B) :
    Real.log (gaussAbs (FinitePlace.mk la) A) - Real.log (gaussAbs (FinitePlace.mk la) B) =
      -((m : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℕ)) := by
  set w := FinitePlace.mk la
  have hS0 : MvPolynomial.map (algebraMap (𝓞 K) K) S ≠ 0 := by
    intro h0; have := gaussAbs_prim la S hS; rw [h0] at this; simp [gaussAbs] at this
  have hX0 : MvPolynomial.map (algebraMap (𝓞 K) K) X ≠ 0 := by
    intro h0; have := gaussAbs_prim la X hX; rw [h0] at this; simp [gaussAbs] at this
  have hN : (0 : ℝ) < ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact_mod_cast (zero_lt_one.trans this)
  have hϖ0 : (ϖ : K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact (inv_pos.2 hN).ne' hϖ.symm
  have hC0 : (C ((ϖ : K) ^ m) : MvPolynomial σ K) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact pow_ne_zero _ hϖ0
  have key := congrArg (gaussAbs w) h
  rw [gauss_abs_mul w _ _ hA hS0, gauss_abs_mul w _ _ (mul_ne_zero hC0 hX0) hB,
    gauss_abs_mul w _ _ hC0 hX0, gaussAbs_prim la S hS, gaussAbs_prim la X hX, gaussAbs_C,
    map_pow, hϖ, mul_one, mul_one] at key
  have hA' := gauss_abs_pos_of_ne_zero w A hA
  have hB' := gauss_abs_pos_of_ne_zero w B hB
  rw [key, Real.log_mul (pow_ne_zero _ (inv_pos.2 hN).ne') hB'.ne', Real.log_pow, Real.log_inv]
  ring

end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def nLa (h : d.S1) (c : ι) (la : HeightOneSpectrum (𝓞 K)) (y : OmS (Ω c) d.D d.N) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)

theorem algK_eq (k : K) : algebraMap K (KTf K d.D d.N) k =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (C k) := by
  first
  | rfl
  | exact IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) k
  | simp [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) k]

theorem pf_fin (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0)
    (PA PB : KTp K d.D d.N) (hA : PA ≠ 0) (hB : PB ≠ 0)
    (hAB : letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PB =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PA)
    (la : HeightOneSpectrum (𝓞 K)) :
    Real.log (gaussAbs (FinitePlace.mk la) PA) - Real.log (gaussAbs (FinitePlace.mk la) PB) =
      -((d.nLa h c la y : ℝ) * logNorm la) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ⟩ := exists_unif la
  obtain ⟨u, hu, hN⟩ := d.norm_at_la hd h c la ϖ hϖ1 hϖ2 y hy
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl u
  dsimp only at hu hN
  have hx : x ∈ (laT d.D d.N la).primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (Op d.D d.N la) (laT d.D d.N la) x s).1 hu
  set g := (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)).comp (OTtoKT K d.D d.N)
  have hspec : g x = g s * OpToKT d.D d.N la (IsLocalization.mk' (Op d.D d.N la) x s) :=
    (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
  set n : ℤ := ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℤ) * WithTop.untopD 0 (w y) with hn
  have hn' : d.nLa h c la y = n := rfl
  set X' : KTp K d.D d.N := OTtoKT K d.D d.N x
  set S' : KTp K d.D d.N := OTtoKT K d.D d.N (s : OT K d.D d.N)
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)

  have hmain : algebraMap _ (KTf K d.D d.N) PA * algebraMap _ (KTf K d.D d.N) S' =
      (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^ n * algebraMap _ (KTf K d.D d.N) X' *
        algebraMap _ (KTf K d.D d.N) PB := by
    rw [← hAB, hN]
    have : algebraMap _ (KTf K d.D d.N) X' = g x := rfl
    have h2 : algebraMap _ (KTf K d.D d.N) S' = g s := rfl
    rw [this, h2, hspec]; ring
  have hlogN : logNorm la = Real.log ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := rfl
  have hxm : x ∉ Ideal.map (C : 𝓞 K →+* OT K d.D d.N) la.asIdeal := hx
  have hsm : (s : OT K d.D d.N) ∉ Ideal.map (C : 𝓞 K →+* OT K d.D d.N) la.asIdeal := s.2
  rw [hn', hlogN]
  have hϖ0 : algebraMap K (KTf K d.D d.N) (ϖ : K) ≠ 0 := by
    rw [map_ne_zero]; intro h0'; rw [h0', map_zero] at hϖ
    have := NumberField.HeightOneSpectrum.one_lt_absNorm la
    have hN0 : (0 : ℝ) < ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast (zero_lt_one.trans this)
    exact (inv_pos.2 hN0).ne' hϖ.symm
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hm] at hmain ⊢
    have hp : PA * S' = C ((ϖ : K) ^ m) * X' * PB := by
      apply hinj
      rw [map_mul, map_mul, map_mul, ← d.algK_eq, map_pow, hmain, zpow_natCast]
    have := log_gauss_ratio la ϖ hϖ PA PB hA hB x s hxm hsm m hp
    rw [this]; push_cast; ring
  · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat h0.le
    have hp : PB * X' = C ((ϖ : K) ^ m) * S' * PA := by
      apply hinj
      rw [map_mul, map_mul, map_mul, ← d.algK_eq, map_pow]
      rw [hm, zpow_neg, zpow_natCast] at hmain
      have hpow : (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^ m ≠ 0 := pow_ne_zero _ hϖ0
      field_simp at hmain
      first
      | linear_combination hmain
      | linear_combination -hmain
    have := log_gauss_ratio la ϖ hϖ PB PA hB hA s x hsm hxm m hp
    rw [hm]; push_cast; linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0

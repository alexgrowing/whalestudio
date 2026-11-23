import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem prod_zpow_single {M : Type*} [CommGroupWithZero M] (f : ι → M) (k₀ : ι) :
    ∏ k, f k ^ ((Pi.single k₀ 1 : ι → ℤ) k) = f k₀ := by
  rw [Finset.prod_eq_single k₀ (fun k _ hk ↦ by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h ↦ absurd (Finset.mem_univ k₀) h), Pi.single_eq_same, zpow_one]

omit [Fintype ι] in
theorem single_cast (k₀ k : ι) : (((Pi.single k₀ 1 : ι → ℕ) k : ℕ) : ℤ) = (Pi.single k₀ 1 : ι → ℤ) k := by
  by_cases h : k = k₀
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

namespace ArithVariety

variable (n : ι → ℕ)

omit [Fintype ι] in
theorem whole_isLive (c : (k : ι) → Fin (n k + 1)) : (whole n).IsLive c := fun _ h ↦
  X_ne_zero _ ((Submodule.mem_bot _).mp h)

omit [Fintype ι] in
theorem whole_mkF_X_ne_zero (v : Coord n) : (whole n).mkF (X v) ≠ 0 := fun h ↦
  X_ne_zero v ((Submodule.mem_bot _).mp (((whole n).mkF_eq_zero_iff _).mp h))

omit [Fintype ι] in
theorem whole_mkF_injective : Function.Injective (whole n).mkF := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  exact (Submodule.mem_bot _).mp (((whole n).mkF_eq_zero_iff f).mp hf)

omit [Fintype ι] in

theorem whole_isHomogGenerators :
    (whole n).IsHomogGenerators (fun i : Fin 0 ↦ i.elim0) (fun i : Fin 0 ↦ i.elim0) where
  homog i := i.elim0
  span_eq := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    rfl

end ArithVariety

variable (n : ι → ℕ) (k₀ : ι)

def blockAddData : AddBlockData (ArithVariety.whole n) where
  deg := Pi.single k₀ 1
  size := n k₀
  elt j := (ArithVariety.whole n).mkF (X ⟨k₀, j⟩)
  elt_deg j := ⟨X ⟨k₀, j⟩, 1, (Pi.single k₀ 1 : ι → ℕ), 0, isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩,
    isWeightedHomogeneous_one ℤ (coordDeg n), fun k ↦ by simp [single_cast],
    (Ideal.ne_top_iff_one _).mp (ArithVariety.whole n).isPrime.ne_top, by rw [map_one, div_one]⟩
  chart_mem c _ j := by
    rw [ArithVariety.chartPow, prod_zpow_single]
    exact Subring.subset_closure ⟨⟨k₀, j⟩, rfl⟩
  generating c _ := by
    refine ⟨Pi.single (c k₀) 1, fun j ↦ ?_, ?_⟩
    · by_cases h : j = c k₀
      · subst h; rw [Pi.single_eq_same]; exact Subring.one_mem _
      · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _
    · rw [Finset.sum_eq_single (c k₀) (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h ↦ absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
        ArithVariety.chartPow, prod_zpow_single]
      exact div_self (ArithVariety.whole_mkF_X_ne_zero n _)

def blockForms : ((k : ι) → Fin (n k + 1)) → Fin ((blockAddData n k₀).size + 1) →
    MvPolynomial (Coord n) ℤ :=
  fun c j ↦ chartMonomial c 1 * X ⟨k₀, j⟩

theorem blockForms_isFormSystem : (blockAddData n k₀).IsFormSystem 1 (blockForms n k₀) where
  pos _ := le_rfl
  nonneg k := by
    have : (0 : ℤ) ≤ (Pi.single k₀ 1 : ι → ℤ) k := by
      by_cases h : k = k₀
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    change (0 : ℤ) ≤ ((1 : ι → ℕ) k : ℤ) + (Pi.single k₀ 1 : ι → ℤ) k
    simp only [Pi.one_apply, Nat.cast_one]
    linarith
  homog c j := ⟨1 + (Pi.single k₀ 1 : ι → ℕ),
    (isWeightedHomogeneous_chartMonomial c 1).mul (isWeightedHomogeneous_X ℤ (coordDeg n) _),
    fun k ↦ by
      change (((1 : ι → ℕ) + (Pi.single k₀ 1 : ι → ℕ)) k : ℤ) = ((1 : ι → ℕ) k : ℤ) + (Pi.single k₀ 1 : ι → ℤ) k
      rw [Pi.add_apply, Nat.cast_add, single_cast]⟩
  value c _ j := by simp only [blockForms, map_mul]; rfl
  dead c hc := absurd (ArithVariety.whole_isLive n c) hc

def blockLine : HermLine n where
  deg := Pi.single k₀ 1
  metric z := l2Norm (z k₀)
  metric_pos z hz := vectorL2Norm_pos (hz k₀)
  metric_smul c z _ _ := by
    rw [vectorL2Norm_const_mul, prod_zpow_single (fun k ↦ ‖c k‖) k₀]
  metric_smooth := contDiffOn_l2Norm_block k₀

def blockVal : Coord (blockAddData n k₀).extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => X ⟨k₀, j⟩
  | ⟨some k, i⟩ => X ⟨k, i⟩

def blockSubst :
    MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ →+* MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (blockVal n k₀ v) * X v.1

theorem blockAddData_extMap :
    (blockAddData n k₀).extMap = (MvPolynomial.map (ArithVariety.whole n).mkF).comp (blockSubst n k₀) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun v ↦ ?_)
  · simp [AddBlockData.extMap, blockSubst]
  · rw [RingHom.comp_apply, AddBlockData.extMap, blockSubst, eval₂Hom_X', eval₂Hom_X', map_mul, map_C, map_X]
    rcases v with ⟨_ | k, i⟩ <;> rfl

theorem blockSubst_eq_zero {f : MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ}
    (hf : f ∈ (blockAddData n k₀).extIdeal) : blockSubst n k₀ f = 0 := by
  have h : (MvPolynomial.map (ArithVariety.whole n).mkF) (blockSubst n k₀ f) = 0 := by
    rw [← RingHom.comp_apply, ← blockAddData_extMap]
    exact RingHom.mem_ker.mp hf
  exact map_injective _ (ArithVariety.whole_mkF_injective n) (h.trans (map_zero _).symm)

theorem blockAddData_joinPt_mem (z : Cone n ℂ) (hz : BlockNonzero z) :
    (blockAddData n k₀).joinPt z (z k₀) ∈ (blockAddData n k₀).extPoints := by
  refine ⟨fun o ↦ ?_, fun f hf ↦ ?_⟩
  · cases o with
    | none => exact hz k₀
    | some k => exact hz k
  · let ev : MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) →+* ℂ :=
      eval₂Hom (eval₂Hom (Int.castRingHom ℂ) fun v ↦ z v.1 v.2) fun _ ↦ 1
    have hev : (eval₂Hom (Int.castRingHom ℂ) fun v : Coord (blockAddData n k₀).extSizes ↦
        (blockAddData n k₀).joinPt z (z k₀) v.1 v.2) = ev.comp (blockSubst n k₀) := by
      refine MvPolynomial.ringHom_ext (fun r ↦ by simp [ev, blockSubst]) (fun v ↦ ?_)
      rcases v with ⟨_ | k, i⟩ <;> simp [ev, blockSubst, blockVal, AddBlockData.joinPt]
    change (eval₂Hom (Int.castRingHom ℂ) fun v : Coord (blockAddData n k₀).extSizes ↦
        (blockAddData n k₀).joinPt z (z k₀) v.1 v.2) f = 0
    rw [hev, RingHom.comp_apply, blockSubst_eq_zero n k₀ hf, map_zero]

theorem blockForms_not_mem (c : (k : ι) → Fin (n k + 1)) (j : Fin ((blockAddData n k₀).size + 1)) :
    (blockAddData n k₀).liftOld (blockForms n k₀ c j) ∉ (blockAddData n k₀).extIdeal := by
  intro h
  have h2 := blockSubst_eq_zero n k₀ h
  simp [blockForms, chartMonomial, AddBlockData.liftOld, AddBlockData.oldCoord, blockSubst, blockVal,
    Finset.prod_eq_zero_iff, X_ne_zero] at h2

omit [Fintype ι] [DecidableEq ι] in

theorem blockNonzero_one : BlockNonzero (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) :=
  fun _ h ↦ one_ne_zero (congrFun h 0)

theorem evalCone_one_blockForms (c : (k : ι) → Fin (n k + 1)) (j : Fin ((blockAddData n k₀).size + 1)) :
    evalCone (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) (blockForms n k₀ c j) ≠ 0 := by
  simp [evalCone, blockForms, chartMonomial]

omit [Fintype ι] [DecidableEq ι] in
theorem evalCone_mul {F : Type*} [CommRing F] (z : Cone n F) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := eval₂_mul _ _

theorem chartSection_toFun_ne_zero (c : (k : ι) → Fin (n k + 1)) :
    (IntegralSection.chartSection (ArithVariety.whole n) c).toFun ≠ 0 := by
  change (ArithVariety.whole n).mkF (chartMonomial c 1) / (ArithVariety.whole n).mkF 1 ≠ 0
  rw [map_one, div_one, Ne, ArithVariety.mkF_eq_zero_iff]
  change ¬ (_ ∈ (⊥ : Ideal (MvPolynomial (Coord n) ℤ)))
  rw [Submodule.mem_bot, chartMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero _)

omit [DecidableEq ι] in
theorem standard_quot_deg :
    (0 : ι → ℤ) = (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv).deg := by
  funext k
  simp [HermLine.pow, HermLine.mul, HermLine.inv, HermLine.standard]

theorem one_supNormLE :
    ((IntegralSection.one (ArithVariety.whole n)).cast (standard_quot_deg n)).SupNormLE
      (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv) 0 := by
  intro z hz c' d' e he hc'
  have he' : e = chartMonomial c' d' := by
    have h := (Submodule.mem_bot _).mp he.2
    change 1 * e - 1 * chartMonomial c' d' = 0 at h
    linear_combination h
  have hne : evalCone z (chartMonomial c' d') ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc' k)
  have hpos : 0 < (HermLine.standard n).metric z := (HermLine.standard n).metric_pos z hz.1
  have hm : (((HermLine.standard n).pow 1).mul (HermLine.standard n).inv).metric z = 1 := by
    change (HermLine.standard n).metric z ^ 1 * ((HermLine.standard n).metric z)⁻¹ = 1
    rw [pow_one, mul_inv_cancel₀ hpos.ne']
  rw [he', hm, mul_one, div_self (norm_ne_zero_iff.mpr hne), Real.exp_zero]

theorem one_toFun_ne_zero (P : ArithVariety n) : (IntegralSection.one P).toFun ≠ 0 := by
  change P.mkF 1 / P.mkF 1 ≠ 0
  rw [map_one, div_one]
  exact one_ne_zero

theorem whole_ringKrullDim (N : ℕ) :
    ringKrullDim (ArithVariety.whole (fun _ : Unit ↦ N)).CoordRing =
      ((N + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq
      (show (ArithVariety.whole (fun _ : Unit ↦ N)).ideal = ⊥ from rfl)).trans (RingEquiv.quotientBot _)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have hc : Nat.card (Coord (fun _ : Unit ↦ N)) = N + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hc, Fintype.card_unit]
  norm_cast
  omega

def gaussianIntegerBasis : Module.Basis (Fin (1 + 1)) ℤ (𝓞 GaussianField) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  haveI : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  haveI : IsCyclotomicExtension {4} ℚ GaussianField := CyclotomicField.isCyclotomicExtension 4 ℚ
  exact (IsCyclotomicExtension.zeta_spec 4 ℚ GaussianField).integralPowerBasis.basis.reindex
    (finCongr (by rw [IsPrimitiveRoot.integralPowerBasis_dim]; decide))

def ratIntegerBasis : Module.Basis (Fin (0 + 1)) ℤ (𝓞 ℚ) :=
  (Module.Basis.singleton (Fin 1) ℤ).map Rat.ringOfIntegersEquiv.symm.toAddEquiv.toIntLinearEquiv

theorem ratIntegerBasis_apply (a : Fin (0 + 1)) : ((ratIntegerBasis a : 𝓞 ℚ) : ℚ) = 1 := by
  simp [ratIntegerBasis, Module.Basis.singleton_apply]

open Matrix in

theorem ratStandard_metricAgrees (r : ℕ) :
    OneBlockMetricAgrees ratIntegerBasis (HermLattice.standard ℚ (r + 1))
      (HermLine.standard (oneBlockSizes 0 r)) := by
  intro σ w _
  change ∏ _u : Unit, l2Norm (oneBlockPoint ratIntegerBasis σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  rw [Fintype.prod_unique, l2Norm, one_mulVec]
  congr 1
  have h1 : ∀ p, ‖oneBlockPoint ratIntegerBasis σ w () p‖ ^ 2 = ‖w (oneBlockIndex 0 r p).2‖ ^ 2 := by
    intro p
    simp [oneBlockPoint, ratIntegerBasis_apply]
  simp only [h1]
  rw [Fintype.sum_equiv (oneBlockIndex 0 r) _ (fun q ↦ ‖w q.2‖ ^ 2) (fun _ ↦ rfl),
    Fintype.sum_prod_type, Fin.sum_univ_one, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem int_span_norm_ge (x : ℝ) (hx : x ∈ Submodule.span ℤ ({1} : Set ℝ)) (h0 : x ≠ 0) :
    Real.exp (-0) ≤ ‖x‖ := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [neg_zero, Real.exp_zero, zsmul_eq_mul, mul_one, Real.norm_eq_abs]
  have ha : a ≠ 0 := by rintro rfl; simp at h0
  exact_mod_cast Int.one_le_abs ha

theorem linearIndependent_one_real : LinearIndependent ℝ ![(1 : ℝ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  simpa using hg

end

end GroundTheory.Heights₂.Heights

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CoordinateConeArithVar

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mConeMap_monomial (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : ℤ) :
    mConeMap y (monomial e a) =
      monomial (e.mapDomain Sigma.fst) ((a : Ω) * e.prod fun p n ↦ y p ^ n) := by
  rw [mConeMap, aeval_monomial, monomial_eq, map_mul, mul_assoc]
  congr 1
  · have h1 : (e.prod fun p n ↦ (C (y p) * X p.1 : MvPolynomial K Ω) ^ n) =
        (e.prod fun p n ↦ C (y p ^ n)) * e.prod fun p n ↦ (X p.1 : MvPolynomial K Ω) ^ n := by
      rw [← Finsupp.prod_mul]
      refine Finsupp.prod_congr fun p _ ↦ ?_
      rw [mul_pow, map_pow]
    rw [h1, Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
    congr 1
    rw [map_finsuppProd]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem coe_mapDomain_fst [DecidableEq K] (e : (Σ k, ι k) →₀ ℕ) :
    ⇑(e.mapDomain Sigma.fst) = Finsupp.weight (NumbersDVR.blockWeight ι) e := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finsupp.finsetSum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp [NumbersDVR.blockWeight, Finsupp.single_apply, Pi.single_apply, eq_comm]

omit [∀ k, Fintype (ι k)] in

theorem component_mem [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : MRing ι)
    (hf : f ∈ mCoordIdeal y) (m : K → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) m f ∈ mCoordIdeal y := by
  classical
  set φ := mConeMap y
  set m' : K →₀ ℕ := Finsupp.equivFunOnFinite.symm m
  have hdeg : ∀ e : (Σ k, ι k) →₀ ℕ,
      e.mapDomain Sigma.fst = m' ↔ Finsupp.weight (NumbersDVR.blockWeight ι) e = m := by
    intro e
    rw [← coe_mapDomain_fst, ← DFunLike.coe_fn_eq, Finsupp.coe_equivFunOnFinite_symm]
  set S := f.support.filter fun e ↦ Finsupp.weight (NumbersDVR.blockWeight ι) e = m
  have himg : φ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) m f) =
      monomial m' (∑ e ∈ S, ((coeff e f : ℤ) : Ω) * e.prod fun p n ↦ y p ^ n) := by
    rw [weightedHomogeneousComponent_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [mConeMap_monomial, (hdeg e).2 (Finset.mem_filter.1 he).2]
  have hcoeff : coeff m' (φ f) = ∑ e ∈ S, ((coeff e f : ℤ) : Ω) * e.prod fun p n ↦ y p ^ n := by
    conv_lhs => rw [f.as_sum, map_sum]
    rw [coeff_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [mConeMap_monomial, coeff_monomial]
    exact if_congr (hdeg e) rfl rfl
  have hzero : φ f = 0 := (RingHom.mem_ker).1 hf
  rw [mCoordIdeal, RingHom.mem_ker]
  show φ _ = 0
  rw [himg, ← hcoeff, hzero, coeff_zero, monomial_zero]

theorem isMultiHomogIdeal (y : (Σ k, ι k) → Ω) : IsMultiHomogIdeal (mCoordIdeal y) := by
  classical
  exact (Bridge.isMultiHomogIdeal_iff _).mp fun f hf m ↦ component_mem y f hf m

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem relevant (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    IsRelevant (mCoordIdeal y) := by
  intro k
  refine ⟨c k, fun h ↦ ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X] at h
  exact mul_ne_zero (by rw [Ne, C_eq_zero]; exact hc k) (X_ne_zero _) h

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem horizontal [CharZero Ω] (y : (Σ k, ι k) → Ω) : IsHorizontal (mCoordIdeal y) := by
  rw [IsHorizontal, eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes,
    MvPolynomial.algebraMap_apply, C_eq_zero, eq_intCast] at ha
  exact (Ideal.mem_bot).mpr (by exact_mod_cast ha)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem algebraMap_injective (I : Ideal (MRing ι)) (h : IsHorizontal I) :
    Function.Injective (algebraMap ℤ (MRing ι ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* MRing ι) := ha
  rw [show I.comap (C : ℤ →+* MRing ι) = ⊥ from h] at h'
  exact (Submodule.mem_bot ℤ).mp h'

def ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω :=
  fun p ↦ y p / y ⟨p.1, c p.1⟩

def scaleT (a : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k ↦ C (a k) * X k

omit [Fintype K] in

theorem scaleT_inv (a : K → Ω) (ha : ∀ k, a k ≠ 0) (g : MvPolynomial K Ω) :
    scaleT (fun k ↦ (a k)⁻¹) (scaleT a g) = g := by
  have h : (scaleT (fun k ↦ (a k)⁻¹)).comp (scaleT a) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k ↦ ?_
    simp only [AlgHom.comp_apply, scaleT, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (ha k), C_1, one_mul]
  exact congrArg (fun φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω ↦ φ g) h

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mConeMap_eq_scale (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (f : MRing ι) :
    mConeMap y f = scaleT (fun k ↦ y ⟨k, c k⟩) (mConeMap (ratioPt y c) f) := by
  have h : (mConeMap y : MRing ι →+* MvPolynomial K Ω) =
      (scaleT fun k ↦ y ⟨k, c k⟩ : MvPolynomial K Ω →+* MvPolynomial K Ω).comp
        (mConeMap (ratioPt y c) : MRing ι →+* MvPolynomial K Ω) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun p ↦ ?_)
    · simp [mConeMap, scaleT]
    · simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, mConeMap, aeval_X, scaleT,
        map_mul, aeval_C, MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ratioPt]
      rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc p.1)]
  exact RingHom.congr_fun h f

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mCoordIdeal_ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    mCoordIdeal y = mCoordIdeal (ratioPt y c) := by
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_eq_scale y c hc]
  constructor
  · intro h
    have h2 := congrArg (scaleT fun k ↦ (y ⟨k, c k⟩)⁻¹) h
    rwa [scaleT_inv _ hc, map_zero] at h2
  · intro h
    rw [h, map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mCoordIdeal_comp {L : Type} [Field L] (σ : L →+* Ω) (z : (Σ k, ι k) → L) :
    mCoordIdeal (fun p ↦ σ (z p)) = mCoordIdeal z := by
  have h : ∀ f, mConeMap (fun p ↦ σ (z p)) f = MvPolynomial.map σ (mConeMap z f) := by
    have e : (mConeMap (fun p ↦ σ (z p)) : MRing ι →+* MvPolynomial K Ω) =
        (MvPolynomial.map σ).comp (mConeMap z : MRing ι →+* MvPolynomial K L) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun p ↦ ?_) <;> simp [mConeMap]
    exact fun f ↦ RingHom.congr_fun e f
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, h]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective σ σ.injective)

abbrev ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ (coneRatios y c)

def ratioPtL [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → ratioField y c :=
  fun p ↦ ⟨ratioPt y c p, IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mCoordIdeal_ratioPtL [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : mCoordIdeal (ratioPtL y c) = mCoordIdeal y := by
  rw [mCoordIdeal_ratioPt y c hc, ← mCoordIdeal_comp (algebraMap (ratioField y c) Ω)]
  rfl

omit [Fintype K] in

theorem rep_of_mem [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ ratioField y c) :
    ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      aeval (ratioPt y c) h ≠ 0 ∧ aeval (ratioPt y c) g = x * aeval (ratioPt y c) h := by
  classical
  suffices H : ∃ (d : K → ℕ) (g h : MRing ι),
      IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g d ∧
      IsWeightedHomogeneous (NumbersDVR.blockWeight ι) h d ∧
      aeval (ratioPt y c) h ≠ 0 ∧ aeval (ratioPt y c) g = x * aeval (ratioPt y c) h by
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := H
    exact ⟨d, g, h, (Bridge.isMultiHomog_iff g d).mp hg, (Bridge.isMultiHomog_iff h d).mp hh, h0, he⟩
  have hz : ∀ k, ratioPt y c ⟨k, c k⟩ = 1 := fun k ↦ div_self (hc k)
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨NumbersDVR.blockWeight ι p, X p, X ⟨p.1, c p.1⟩, isWeightedHomogeneous_X _ _ _,
      isWeightedHomogeneous_X _ _ _, ?_, ?_⟩
    · rw [aeval_X, hz]
      exact one_ne_zero
    · rw [aeval_X, aeval_X, hz, mul_one]
      rfl
  | algebraMap q =>
    refine ⟨0, C q.num, C (q.den : ℤ), isWeightedHomogeneous_C _ _, isWeightedHomogeneous_C _ _, ?_, ?_⟩
    · simp
    · have hd : ((q.den : ℤ) : Ω) ≠ 0 := by exact_mod_cast q.den_nz
      rw [aeval_C, aeval_C, algebraMap_int_eq, eq_intCast, eq_intCast, eq_ratCast, Rat.cast_def]
      push_cast at hd ⊢
      field_simp
  | add x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, n₁, e₁⟩ := ih₁
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, n₂, e₂⟩ := ih₂
    have hg₂₁ := hg₂.mul hh₁
    rw [add_comm d₂ d₁] at hg₂₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, (hg₁.mul hh₂).add hg₂₁, hh₁.mul hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero n₁ n₂
    · rw [map_add, map_mul, map_mul, map_mul, e₁, e₂]
      ring
  | inv x _ ih =>
    obtain ⟨d, g, h, hg, hh, n, e⟩ := ih
    by_cases hx0 : x = 0
    · refine ⟨d, 0, h, isWeightedHomogeneous_zero _ _ _, hh, n, ?_⟩
      simp [hx0]
    · have ng : aeval (ratioPt y c) g ≠ 0 := by
        rw [e]
        exact mul_ne_zero hx0 n
      refine ⟨d, h, g, hh, hg, ng, ?_⟩
      rw [e, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, n₁, e₁⟩ := ih₁
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, n₂, e₂⟩ := ih₂
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, hg₁.mul hg₂, hh₁.mul hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero n₁ n₂
    · rw [map_mul, map_mul, e₁, e₂]
      ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem coe_aeval_ratioPtL [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    ((aeval (ratioPtL y c) f : ratioField y c) : Ω) = aeval (ratioPt y c) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp, ratioPtL]

omit [Fintype K] in

theorem birational [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Birational (ratioPtL y c) := by
  intro s
  obtain ⟨d, g, h, hg, hh, n, e⟩ := rep_of_mem y c hc s.2
  refine ⟨d, g, h, hg, hh, fun h0 ↦ n ?_, Subtype.ext ?_⟩
  · rw [← coe_aeval_ratioPtL, h0]
    rfl
  · rw [coe_aeval_ratioPtL, IntermediateField.coe_mul, coe_aeval_ratioPtL, e]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem trdeg_ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : ℕ) (t : Fin d → Ω)
    (ht : AlgebraicIndependent ℚ t) (htL : ∀ i, t i ∈ ratioField y c)
    (halg : ∀ r ∈ coneRatios y c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r) :
    Algebra.trdeg ℤ (ratioField y c) = d := by
  set L := ratioField y c
  let t' : Fin d → L := fun i ↦ ⟨t i, htL i⟩
  have hind : AlgebraicIndependent ℚ t' := AlgebraicIndependent.of_comp L.val ht
  set F := IntermediateField.adjoin ℚ (Set.range t)
  have hLe : L ≤ (algebraicClosure F Ω).restrictScalars ℚ := by
    rw [IntermediateField.adjoin_le_iff]
    intro r hr
    exact (IntermediateField.mem_restrictScalars _).mpr
      ((mem_algebraicClosure_iff).mpr (halg r hr))
  have hbasis : IsTranscendenceBasis ℚ t' := by
    refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun x ↦ ?_⟩
    by_contra hx
    have h1 : AlgebraicIndependent ℚ (fun o : Option (Fin d) ↦ o.elim x t') :=
      (hind.option_iff_transcendental x).mpr hx
    have h2 : AlgebraicIndependent ℚ (fun o : Option (Fin d) ↦ o.elim (x : Ω) t) := by
      have h3 := h1.map' (f := L.val) (fun a b hab ↦ Subtype.ext hab)
      convert h3 using 1
      funext o
      cases o <;> rfl
    refine (ht.option_iff_transcendental (x : Ω)).mp h2 ?_
    have hxF : IsAlgebraic F (x : Ω) :=
      (mem_algebraicClosure_iff).mp
        ((IntermediateField.mem_restrictScalars _).mp (hLe x.2))
    exact (IntermediateField.isAlgebraic_adjoin_iff).mp hxF
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have hZ : IsTranscendenceBasis ℤ t' := (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℤ ℚ).mpr hbasis
  rw [← hZ.cardinalMk_eq_trdeg, Cardinal.mk_fin]

end CoordinateConeArithVar

open CoordinateConeArithVar in

theorem CoordConeArithVar.proof (hDim : IntDomainDim.Statement) : CoordConeArithVar.Statement := by
  intro K _ ι _ Ω _ _ y c d t hK hc ht htL halg
  have hprime : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  refine ⟨hK, ⟨hprime, isMultiHomogIdeal y, relevant y c hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.proof K ι (ratioField y c) (ratioPtL y c) (birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [mCoordIdeal_ratioPtL y c hc, trdeg_ratioField y c d t ht htL halg] at htr
  have hA := hDim (MRing ι ⧸ mCoordIdeal y) (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add, map_natCast]
  norm_cast
  omega

end

end GroundTheory.Heights₂.Heights

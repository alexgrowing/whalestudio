import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.PowLeComapMapPow

open Polynomial

namespace GlobalTheory

universe u

noncomputable abbrev normIntegers (C : Type*) [NormedField C] [IsUltrametricDist C] :
    ValuationSubring C :=
  (NormedField.valuation (K := C)).valuationSubring

theorem mem_normIntegers_iff {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C} :
    x ∈ normIntegers C ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem normIntegers_integers (C : Type*) [NormedField C] [IsUltrametricDist C] :
    (NormedField.valuation (K := C)).Integers (normIntegers C) :=
  Valuation.valuationSubring.integers _

section Extend

variable {A B : Type*} [CommRing A] [CommRing B]

theorem adicCompletion_ringHom_ext_of_fg (I : Ideal A) (hI : I.FG) (f : A →+* B)
    [IsHausdorff (I.map f) B] {g₁ g₂ : AdicCompletion I A →+* B}
    (h₁ : g₁.comp (algebraMap A _) = f) (h₂ : g₂.comp (algebraMap A _) = f) : g₁ = g₂ := by
  ext x
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I.map f)
  intro n
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.1 n)
  have hx : x - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hI, AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  have key : ∀ g : AdicCompletion I A →+* B, g.comp (algebraMap A _) = f →
      g x - f a ∈ (I.map f) ^ n := by
    intro g hg
    have := Ideal.mem_map_of_mem g hx
    rw [Ideal.map_map, hg, Ideal.map_pow, map_sub] at this
    rwa [← hg, RingHom.comp_apply, hg]
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  simpa using Ideal.sub_mem _ (key g₁ h₁) (key g₂ h₂)

theorem exists_adicCompletion_ringHom_extend (I : Ideal A) (f : A →+* B)
    [IsAdicComplete (I.map f) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A _) = f := by
  first
  | exact @_root_.GlobalTheory.PowerExtensionEvaluation.exists_extension
  | exact _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension
  | (apply _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerExtensionEvaluation.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension ..)

theorem existsUnique_adicCompletion_ringHom_extend (I : Ideal A) (hI : I.FG) (f : A →+* B)
    [IsAdicComplete (I.map f) B] :
    ∃! g : AdicCompletion I A →+* B, g.comp (algebraMap A _) = f := by
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend I f
  exact ⟨g, hg, fun g' hg' => adicCompletion_ringHom_ext_of_fg I hI f hg' hg⟩

end Extend

namespace NormIntegers

section Basic

variable {C : Type*} [NormedField C] [IsUltrametricDist C] {O : Type*} [CommRing O] [Algebra O C]
  (hO : (NormedField.valuation (K := C)).Integers O)
include hO

theorem norm_le_one (x : O) : ‖algebraMap O C x‖ ≤ 1 := by
  simpa [← NNReal.coe_le_coe] using hO.map_le_one x

theorem exists_of_norm_le_one {x : C} (hx : ‖x‖ ≤ 1) : ∃ y : O, algebraMap O C y = x :=
  hO.exists_of_le_one (by simpa [← NNReal.coe_le_coe] using hx)

theorem dvd_iff_norm_le {x y : O} : x ∣ y ↔ ‖algebraMap O C y‖ ≤ ‖algebraMap O C x‖ := by
  rw [hO.dvd_iff_le]; simp [← NNReal.coe_le_coe]

theorem isUnit_iff_norm_eq_one {x : O} : IsUnit x ↔ ‖algebraMap O C x‖ = 1 := by
  rw [hO.isUnit_iff_valuation_eq_one]; simp [← NNReal.coe_inj]

theorem norm_pos_iff {x : O} : 0 < ‖algebraMap O C x‖ ↔ x ≠ 0 := by
  simp [map_eq_zero_iff _ hO.hom_inj]

theorem mem_span_singleton_pow_iff {w x : O} {n : ℕ} :
    x ∈ Ideal.span {w} ^ n ↔ ‖algebraMap O C x‖ ≤ ‖algebraMap O C w‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_iff_norm_le hO, map_pow, norm_pow]

theorem mem_maximalIdeal_iff [IsLocalRing O] {x : O} :
    x ∈ IsLocalRing.maximalIdeal O ↔ ‖algebraMap O C x‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one hO]
  exact (norm_le_one hO x).lt_iff_ne.symm

theorem isDomain : IsDomain O := hO.hom_inj.isDomain

theorem isLocalRing : IsLocalRing O :=
  haveI := isDomain hO
  haveI := ValuationRing.of_integers _ hO
  inferInstance

theorem isPrincipal_of_fg {J : Ideal O} (hJ : J.FG) : J.IsPrincipal :=
  haveI := isDomain hO
  haveI := ValuationRing.of_integers _ hO
  IsBezout.isPrincipal_of_FG J hJ

theorem eq_bot_or_eq_span_of_fg_of_ne_top {J : Ideal O} (hJ : J.FG) (hJ' : J ≠ ⊤) :
    J = ⊥ ∨ ∃ w : O, 0 < ‖algebraMap O C w‖ ∧ ‖algebraMap O C w‖ < 1 ∧ J = Ideal.span {w} := by
  obtain ⟨w, hw⟩ := isPrincipal_of_fg hO hJ
  rw [Ideal.submodule_span_eq] at hw
  by_cases h0 : w = 0
  · left; simp [hw, h0]
  · right
    refine ⟨w, (norm_pos_iff hO).2 h0, (norm_le_one hO w).lt_of_ne fun h => hJ' ?_, hw⟩
    rw [hw, Ideal.span_singleton_eq_top, isUnit_iff_norm_eq_one hO, h]

theorem isHausdorff_span_singleton {w : O} (hw : ‖algebraMap O C w‖ < 1) :
    IsHausdorff (Ideal.span {w}) O where
  haus' x hx := by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff hO] at hx
    have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hw) hx
    by_contra h
    exact absurd this (not_le.2 ((norm_pos_iff hO).2 h))

theorem isAdicComplete_span_singleton [CompleteSpace C] {w : O} (hw : ‖algebraMap O C w‖ < 1) :
    IsAdicComplete (Ideal.span {w}) O where
  toIsHausdorff := isHausdorff_span_singleton hO hw
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff hO,
      map_sub] at hf ⊢
    have hc : CauchySeq fun n => algebraMap O C (f n) := by
      refine cauchySeq_of_le_geometric ‖algebraMap O C w‖ 1 hw fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hf (Nat.le_succ n)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => norm_le_one hO _
    obtain ⟨l, rfl⟩ := exists_of_norm_le_one hO hL1
    refine ⟨l, fun n => ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds.sub hL).norm) ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hf hm

theorem isAdicComplete_of_fg [CompleteSpace C] {J : Ideal O} (hJ : J.FG) (hJ' : J ≠ ⊤) :
    IsAdicComplete J O := by
  rcases eq_bot_or_eq_span_of_fg_of_ne_top hO hJ hJ' with rfl | ⟨w, -, hw, rfl⟩
  · infer_instance
  · exact isAdicComplete_span_singleton hO hw

theorem henselianLocalRing [CompleteSpace C] : HenselianLocalRing O :=
  { toIsLocalRing := isLocalRing hO
    is_henselian := fun f hf a₀ h₁ h₂ => by
      haveI := isLocalRing hO
      haveI := isAdicComplete_span_singleton hO ((mem_maximalIdeal_iff hO).1 h₁)
      obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian (I := Ideal.span {f.eval a₀}) f hf a₀
        (Ideal.mem_span_singleton_self _) (h₂.map _)
      exact ⟨a, ha, (Ideal.span_singleton_le_iff_mem _).2 h₁ ha'⟩ }

theorem existsUnique_extend_of_fg [CompleteSpace C] {A : Type*} [CommRing A] [IsLocalRing A]
    (hA : (IsLocalRing.maximalIdeal A).FG) (f : A →+* O) [IsLocalHom f] :
    ∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* O,
      g.comp (algebraMap A _) = f := by
  haveI := isLocalRing hO
  haveI : IsAdicComplete ((IsLocalRing.maximalIdeal A).map f) O :=
    isAdicComplete_of_fg hO (hA.map f) (IsLocalRing.map_maximalIdeal_lt_top f).ne
  exact existsUnique_adicCompletion_ringHom_extend _ hA f

theorem isAlgClosed_residueField [IsAlgClosed C] [IsLocalRing O] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨q, hq, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (f := IsLocalRing.residue O)
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p) hp
  have hd : (q.map (algebraMap O C)).degree ≠ 0 := by
    rw [hmon.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral O x := ⟨q, hmon, by rwa [IsRoot, eval_map] at hx⟩
  obtain ⟨y, rfl⟩ := hO.exists_of_le_one (hO.mem_of_integral hint)
  have hy : q.eval y = 0 := by
    apply hO.hom_inj
    rw [IsRoot, eval_map, eval₂_at_apply] at hx
    rw [hx, map_zero]
  refine ⟨IsLocalRing.residue O y, ?_⟩
  rw [← hq, eval_map, eval₂_at_apply, hy, map_zero]

end Basic

theorem ringKrullDim_eq_one {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
    {O : Type*} [CommRing O] [Algebra O C] (hO : (NormedField.valuation (K := C)).Integers O) :
    ringKrullDim O = 1 := by
  haveI := isDomain hO
  haveI := isLocalRing hO
  rw [ringKrullDim_eq_one_iff_of_isLocalRing_isDomain]
  constructor
  · obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one C
    obtain ⟨y, rfl⟩ := exists_of_norm_le_one hO hx1.le
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    have : y ∈ IsLocalRing.maximalIdeal O := (mem_maximalIdeal_iff hO).2 hx1
    rw [h, Ideal.mem_bot] at this
    exact (norm_pos_iff hO).1 hx0 this
  · intro x hx y hy
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ((norm_pos_iff hO).2 hx)
      ((mem_maximalIdeal_iff hO).1 hy)
    refine ⟨n, ?_⟩
    rw [Ideal.mem_span_singleton, dvd_iff_norm_le hO, map_pow, norm_pow]
    exact hn.le

end NormIntegers

theorem exists_norm_pow_eq_of_isAlgClosed {C : Type*} [NormedField C] [IsAlgClosed C] (x : C)
    {n : ℕ} (hn : 0 < n) : ∃ y : C, ‖y‖ ^ n = ‖x‖ := by
  obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x hn
  exact ⟨y, (norm_pow y n).symm⟩

theorem valueGroup_divisible_of_isAlgClosed {C : Type*} [Field C] [IsAlgClosed C]
    (O : ValuationSubring C) (γ : O.ValueGroup) {n : ℕ} (hn : 0 < n) :
    ∃ δ : O.ValueGroup, δ ^ n = γ := by
  obtain ⟨x, rfl⟩ := O.valuation_surjective γ
  obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x hn
  exact ⟨O.valuation y, (map_pow _ y n).symm⟩

theorem isLocalHom_of_comp_algebraMap_adicCompletion {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B) (hg : g.comp (algebraMap A _) = f) :
    IsLocalHom g := by
  refine ((IsLocalRing.local_hom_TFAE g).out 0 2).2 ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hg]
  exact ((IsLocalRing.local_hom_TFAE f).out 0 2).1 ‹_›

theorem isAlgClosed_of_denseRange {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L := by
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  letI : NormedField F := spectralNorm.normedField L F
  letI : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have hcl : IsClosed (Set.range (algebraMap L F)) :=
    (algebraMap_isometry L F).isClosedEmbedding.isClosed_range
  have ha : a ∈ Set.range (algebraMap L F) := by
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro δ δpos
    have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
    obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
      exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
    obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
        (by simpa [Polynomial.map_map] using (IsAlgClosed.splits g).map ((algebraMap L F).comp _))
    have hab : ‖a - b‖ < δ := by
      rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
          ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
      · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
      · simp [fnatdeg0]
      · positivity
    refine ⟨b, ?_, by rwa [dist_eq_norm]⟩
    rw [Polynomial.aroots_def, Splits.roots_map ((IsAlgClosed.splits g).map _),
        Multiset.mem_map] at hb
    obtain ⟨c, _, hc⟩ := hb
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := ha
  refine ⟨c, ?_⟩
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hc, map_zero]
  · exact RingHom.injective _

@[reducible] noncomputable def completionNontriviallyNormedField (K : Type*)
    [NontriviallyNormedField K] : NontriviallyNormedField (UniformSpace.Completion K) where
  __ : NormedField (UniformSpace.Completion K) := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨x, by simpa using hx⟩

theorem exists_complete_isAlgClosed_isometry (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (i : K →+* C), ∀ x, ‖i x‖ = ‖x‖ := by
  let K₁ := UniformSpace.Completion K
  letI : NontriviallyNormedField K₁ := completionNontriviallyNormedField K
  haveI : IsUltrametricDist K₁ := IsUltrametricDist.of_normedAlgebra K
  let K₂ := AlgebraicClosure K₁
  letI : NontriviallyNormedField K₂ := spectralNorm.nontriviallyNormedField K₁ K₂
  letI : NormedAlgebra K₁ K₂ := spectralNorm.normedAlgebra K₁ K₂
  haveI : IsUltrametricDist K₂ := IsUltrametricDist.of_normedAlgebra K₁
  let C := UniformSpace.Completion K₂
  letI : NontriviallyNormedField C := completionNontriviallyNormedField K₂
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra K₂
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := K₂) UniformSpace.Completion.denseRange_coe
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap K₂ C).comp ((algebraMap K₁ K₂).comp (algebraMap K K₁)), fun x => ?_⟩
  have h₁ : ∀ y : K₂, ‖algebraMap K₂ C y‖ = ‖y‖ := fun y => UniformSpace.Completion.norm_coe y
  have h₂ : ∀ y : K₁, ‖algebraMap K₁ K₂ y‖ = ‖y‖ := fun y => spectralNorm_extends y
  have h₃ : ∀ y : K, ‖algebraMap K K₁ y‖ = ‖y‖ := fun y => UniformSpace.Completion.norm_coe y
  rw [RingHom.comp_apply, RingHom.comp_apply, h₁, h₂, h₃]

open IsDedekindDomain in

theorem exists_absoluteValue_of_isDiscreteValuationRing (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {a : V} (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∃ w : AbsoluteValue K ℝ, IsNonarchimedean w ∧
      (∀ x : K, w x ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧ w (algebraMap V K a) = r := by
  let v := IsDiscreteValuationRing.maximalIdeal V
  have h0 : v.valuation K (algebraMap V K a) ≠ 0 := by
    simpa using ha0
  have h1 : v.valuation K (algebraMap V K a) < 1 := (v.valuation_lt_one_iff_mem a).2 ha
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero h0) with hm
  have hm0 : m < 0 := by
    rw [← WithZero.coe_unzero h0, ← WithZero.coe_one, WithZero.coe_lt_coe] at h1
    exact h1
  let b : NNReal := ⟨r ^ ((m : ℝ)⁻¹), by positivity⟩
  have hb : 1 < b := by
    rw [← NNReal.coe_lt_coe]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hr0 hr1 (inv_lt_zero.2 (by exact_mod_cast hm0))
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, fun x => ?_, ?_⟩
  · have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one, fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  · change ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap V K a)) :
      NNReal) : ℝ) = r
    rw [WithZeroMulInt.toNNReal_neg_apply _ h0, ← hm, NNReal.coe_zpow]
    change (r ^ ((m : ℝ)⁻¹)) ^ m = r
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, inv_mul_cancel₀ (by exact_mod_cast hm0.ne),
      Real.rpow_one]

theorem exists_complete_isAlgClosed_of_isDiscreteValuationRing (V : Type*) (K : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (_ : Algebra K C),
      (∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧
        ‖algebraMap K C (algebraMap V K a)‖ = r := by
  obtain ⟨w, hw, hw1, hwa⟩ := exists_absoluteValue_of_isDiscreteValuationRing V K ha0 ha hr0 hr1
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w (algebraMap V K a))⁻¹, by
        rw [norm_inv]
        change 1 < (w (algebraMap V K a))⁻¹
        rw [hwa]
        exact (one_lt_inv₀ hr0).2 hr1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => hw x.ofAbs y.ofAbs
  obtain ⟨C, _, _, _, _, i, hi⟩ := exists_complete_isAlgClosed_isometry (WithAbs w)
  letI : Algebra K C := (i.comp (WithAbs.equiv w).symm.toRingHom).toAlgebra
  have hn : ∀ x : K, ‖algebraMap K C x‖ = w x := fun x => hi _
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by rw [hn, hw1], by rw [hn, hwa]⟩

theorem norm_ratCast_eq_padicNorm {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
    (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (q : ℚ) :
    ‖(q : C)‖ = ‖(q : ℚ_[p])‖ := by
  have hlt : ‖(p : C)‖ < 1 := by
    rw [h]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hcop : ∀ m : ℕ, ¬ p ∣ m → ‖(m : C)‖ = 1 := by
    intro m hm
    refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C m) (not_lt.1 fun hm1 => ?_)
    have hc : IsCoprime (p : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
    obtain ⟨s, t, hst⟩ := hc
    have h1 : (s : C) * p + t * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) hst
    have := IsUltrametricDist.norm_add_le_max ((s : C) * p) (t * m)
    rw [h1, norm_one, norm_mul, norm_mul] at this
    refine absurd this (not_le.2 (max_lt ?_ ?_))
    · exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one C s)
        (norm_nonneg _) hlt
    · exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one C t)
        (norm_nonneg _) hm1
  have hnat : ∀ n : ℕ, ‖(n : C)‖ = ‖(n : ℚ_[p])‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
    have hm' : ‖(m : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm
    simp only [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, h, hcop m hm, hm', Padic.norm_p]
  have hint : ∀ n : ℤ, ‖(n : C)‖ = ‖(n : ℚ_[p])‖ := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [hnat]
  rw [Rat.cast_def, Rat.cast_def, norm_div, norm_div, hnat, hint]

theorem exists_padic_isometry {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
    [CompleteSpace C] (p : ℕ) [Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) :
    ∃ j : ℚ_[p] →+* C, ∀ x, ‖j x‖ = ‖x‖ := by
  let w : AbsoluteValue ℚ ℝ := Rat.AbsoluteValue.padic p
  let i : WithAbs w →+* ℚ_[p] := (Rat.castHom ℚ_[p]).comp (WithAbs.equiv w).toRingHom
  let f : WithAbs w →+* C := (Rat.castHom C).comp (WithAbs.equiv w).toRingHom
  have hi : ∀ x, ‖i x‖ = ‖x‖ := fun x => Padic.eq_padicNorm _
  have hf : ∀ x, ‖f x‖ = ‖x‖ := fun x => (norm_ratCast_eq_padicNorm p h _).trans (hi x)
  have hi' : Isometry i := AddMonoidHomClass.isometry_of_norm i hi
  have hf' : Isometry f := AddMonoidHomClass.isometry_of_norm f hf
  have hd : DenseRange i :=
    (Padic.denseRange_ratCast p).mono (by
      rintro _ ⟨q, rfl⟩
      exact ⟨WithAbs.toAbs w q, rfl⟩)
  let j : ℚ_[p] →+* C :=
    IsDenseInducing.extendRingHom hi'.isUniformInducing hd hf'.uniformContinuous
  have hjc : Continuous j :=
    (uniformContinuous_uniformly_extend hi'.isUniformInducing hd hf'.uniformContinuous).continuous
  refine ⟨j, fun x => ?_⟩
  refine hd.induction_on x (isClosed_eq hjc.norm continuous_norm) fun q => ?_
  have : j (i q) = f q :=
    IsDenseInducing.extend_eq (hi'.isUniformInducing.isDenseInducing hd) hf'.continuous q
  rw [this, hf, hi]

theorem norm_padic_ringHom_eq {C : Type*} [NormedField C] (p : ℕ) [hp : Fact p.Prime]
    (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (j : ℚ_[p] →+* C) (hj : ∀ x : ℤ_[p], ‖j x‖ ≤ 1) (x : ℚ_[p]) :
    ‖j x‖ = ‖x‖ := by
  have hu : ∀ y : ℚ_[p], ‖y‖ = 1 → ‖j y‖ = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have h1 : ‖j y‖ ≤ 1 := hj ⟨y, hy.le⟩
    have h2 : ‖j y⁻¹‖ ≤ 1 := hj ⟨y⁻¹, by simp [hy]⟩
    rw [map_inv₀, norm_inv, inv_le_one₀ (by simpa using hy0)] at h2
    exact le_antisymm h1 h2
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have := hu (x * (p : ℚ_[p]) ^ (-x.valuation)) (by
    rw [norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx, inv_zpow,
      mul_inv_cancel₀ (zpow_ne_zero _ hp0)])
  rw [map_mul, map_zpow₀, map_natCast, norm_mul, norm_zpow, h, inv_zpow,
    mul_inv_eq_one₀ (zpow_ne_zero _ hp0)] at this
  rw [this, Padic.norm_eq_zpow_neg_valuation hx]

theorem padic_ringHom_ext_of_continuous {C : Type*} [NormedField C] (p : ℕ) [Fact p.Prime]
    {j₁ j₂ : ℚ_[p] →+* C} (h₁ : Continuous j₁) (h₂ : Continuous j₂) : j₁ = j₂ := by
  refine RingHom.ext fun x => congrFun ((Padic.denseRange_ratCast p).equalizer h₁ h₂ ?_) x
  ext q
  simp

theorem exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing (V : Type*) (K : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]
    (hV : (p : V) ∈ IsLocalRing.maximalIdeal V) :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (_ : NormedAlgebra ℚ_[p] C) (_ : Algebra K C),
      ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range := by
  have hp0 : (p : V) ≠ 0 := fun h => by
    have := congrArg (algebraMap V K) h
    rw [map_natCast, map_zero] at this
    exact hp.out.ne_zero (by exact_mod_cast this)
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hV
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  rw [map_natCast, map_natCast] at hCp
  haveI : CharZero C := charZero_of_injective_ringHom (algebraMap K C).injective
  obtain ⟨j, hj⟩ := exists_padic_isometry p hCp
  letI : Algebra ℚ_[p] C := j.toAlgebra
  letI : NormedAlgebra ℚ_[p] C :=
    { (inferInstance : Algebra ℚ_[p] C) with
      norm_smul_le := fun r x => by
        rw [Algebra.smul_def, norm_mul]
        exact le_of_eq (congrArg (· * ‖x‖) (hj r)) }
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC⟩

theorem exists_isLocalHom_normIntegers {V K C : Type*} [CommRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [NormedField C] [IsUltrametricDist C] [Algebra K C]
    (h : ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) :
    ∃ φ : V →+* normIntegers C, IsLocalHom φ ∧
      ∀ a, (φ a : C) = algebraMap K C (algebraMap V K a) := by
  let φ : V →+* normIntegers C :=
    ((algebraMap K C).comp (algebraMap V K)).codRestrict (normIntegers C) fun a =>
      mem_normIntegers_iff.2 ((h _).2 ⟨a, rfl⟩)
  refine ⟨φ, ⟨fun a ha => ?_⟩, fun _ => rfl⟩
  have h1 : ‖algebraMap K C (algebraMap V K a)‖ = 1 :=
    (NormIntegers.isUnit_iff_norm_eq_one (normIntegers_integers C)).1 ha
  have h0 : algebraMap V K a ≠ 0 := fun h0 => by simp [h0] at h1
  obtain ⟨b, hb⟩ := (h (algebraMap V K a)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective V K ?_)
  rw [map_mul, hb, mul_inv_cancel₀ h0, map_one]

instance {C : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] :
    HenselianLocalRing (normIntegers C) :=
  { (inferInstance : IsLocalRing (normIntegers C)) with
    is_henselian := (NormIntegers.henselianLocalRing (normIntegers_integers C)).is_henselian }

instance {C : Type*} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] :
    IsAlgClosed (IsLocalRing.ResidueField (normIntegers C)) :=
  NormIntegers.isAlgClosed_residueField (normIntegers_integers C)

theorem normIntegers_properties_of_completeSpace (C : Type*) [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] :
    (∀ w : normIntegers C, ‖(w : C)‖ < 1 → IsAdicComplete (Ideal.span {w}) (normIntegers C)) ∧
    (∀ J : Ideal (normIntegers C), J.FG → J.IsPrincipal) ∧
    (∀ J : Ideal (normIntegers C), J.FG → J ≤ IsLocalRing.maximalIdeal (normIntegers C) →
      J = ⊥ ∨ ∃ w : normIntegers C, 0 < ‖(w : C)‖ ∧ ‖(w : C)‖ < 1 ∧ J = Ideal.span {w}) ∧
    HenselianLocalRing (normIntegers C) ∧
    ringKrullDim (normIntegers C) = 1 ∧
    (IsAlgClosed C →
      (∀ (γ : (normIntegers C).ValueGroup) (n : ℕ), 0 < n → ∃ δ, δ ^ n = γ) ∧
      (∀ (x : C) (n : ℕ), 0 < n → ∃ y : C, ‖y‖ ^ n = ‖x‖) ∧
      IsAlgClosed (IsLocalRing.ResidueField (normIntegers C))) ∧
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A →+* normIntegers C) [IsLocalHom f],
      (∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
        g.comp (algebraMap A _) = f) ∧
      ∀ g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
        g.comp (algebraMap A _) = f → IsLocalHom g) := by
  have hO := normIntegers_integers C
  refine ⟨fun w hw => NormIntegers.isAdicComplete_span_singleton hO hw,
    fun J hJ => NormIntegers.isPrincipal_of_fg hO hJ,
    fun J hJ hle => NormIntegers.eq_bot_or_eq_span_of_fg_of_ne_top hO hJ
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle),
    inferInstance, NormIntegers.ringKrullDim_eq_one hO,
    fun _ => ⟨fun γ n hn => valueGroup_divisible_of_isAlgClosed _ γ hn,
      fun x n hn => exists_norm_pow_eq_of_isAlgClosed x hn, inferInstance⟩,
    fun A _ _ _ f _ => ⟨NormIntegers.existsUnique_extend_of_fg hO
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing f,
      fun g hg => isLocalHom_of_comp_algebraMap_adicCompletion f g hg⟩⟩

theorem valuationRing_of_complete_field :
    (∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C],
      (∀ w : normIntegers C, ‖(w : C)‖ < 1 → IsAdicComplete (Ideal.span {w}) (normIntegers C)) ∧
      (∀ J : Ideal (normIntegers C), J.FG → J.IsPrincipal) ∧
      (∀ J : Ideal (normIntegers C), J.FG → J ≤ IsLocalRing.maximalIdeal (normIntegers C) →
        J = ⊥ ∨ ∃ w : normIntegers C, 0 < ‖(w : C)‖ ∧ ‖(w : C)‖ < 1 ∧ J = Ideal.span {w}) ∧
      HenselianLocalRing (normIntegers C) ∧
      ringKrullDim (normIntegers C) = 1 ∧
      (IsAlgClosed C →
        (∀ (γ : (normIntegers C).ValueGroup) (n : ℕ), 0 < n → ∃ δ, δ ^ n = γ) ∧
        (∀ (x : C) (n : ℕ), 0 < n → ∃ y : C, ‖y‖ ^ n = ‖x‖) ∧
        IsAlgClosed (IsLocalRing.ResidueField (normIntegers C))) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        (f : A →+* normIntegers C) [IsLocalHom f],
        (∃! g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
          g.comp (algebraMap A _) = f) ∧
        ∀ g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* normIntegers C,
          g.comp (algebraMap A _) = f → IsLocalHom g)) ∧
    (∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
      [Algebra V K] [IsFractionRing V K],
      (∀ a : V, a ≠ 0 → a ∈ IsLocalRing.maximalIdeal V → ∀ r : ℝ, 0 < r → r < 1 →
        ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C)
          (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra K C),
          (∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧
            ‖algebraMap K C (algebraMap V K a)‖ = r) ∧
      (∀ [CharZero K] (p : ℕ) [Fact p.Prime], (p : V) ∈ IsLocalRing.maximalIdeal V →
        ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C)
          (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : NormedAlgebra ℚ_[p] C) (_ : Algebra K C),
          ∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range)) :=
  ⟨fun C _ _ _ => normIntegers_properties_of_completeSpace C,
    fun V K _ _ _ _ _ _ =>
      ⟨fun _ ha0 ha _ hr0 hr1 =>
        exists_complete_isAlgClosed_of_isDiscreteValuationRing V K ha0 ha hr0 hr1,
      fun p _ hp => exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing V K p hp⟩⟩

end GlobalTheory

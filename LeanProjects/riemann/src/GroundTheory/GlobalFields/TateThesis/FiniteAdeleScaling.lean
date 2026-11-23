import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

namespace GroundTheory.Global

open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise

noncomputable section

theorem measure_eq_card_mul_measure_ker {A Q : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A)
    [μ.IsAddLeftInvariant] (L : AddSubgroup A) [AddGroup Q] [Finite Q] (φ : L →+ Q)
    (hφ : Function.Surjective φ) (hker : IsOpen ((φ.ker.map L.subtype : AddSubgroup A) : Set A)) :
    μ L = Nat.card Q * μ (φ.ker.map L.subtype) := by
  classical
  have := Fintype.ofFinite Q
  set N : Set A := ((φ.ker.map L.subtype : AddSubgroup A) : Set A) with hN
  have hmemN : ∀ y : A, y ∈ N ↔ ∃ h : y ∈ L, φ ⟨y, h⟩ = 0 := by
    intro y
    simp only [hN, AddSubgroup.coe_map, AddSubgroup.coe_subtype, Set.mem_image, SetLike.mem_coe,
      AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨⟨z, hz⟩, h0, rfl⟩
      exact ⟨hz, h0⟩
    · rintro ⟨h, h0⟩
      exact ⟨⟨y, h⟩, h0, rfl⟩
  let t : Q → L := Function.surjInv hφ
  have ht : ∀ q, φ (t q) = q := Function.surjInv_eq hφ
  have hU : (L : Set A) = ⋃ q, ((t q : L) : A) +ᵥ N := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · intro hy
      refine ⟨φ ⟨y, hy⟩, -(t (φ ⟨y, hy⟩) : A) + y, (hmemN _).2 ⟨L.add_mem (L.neg_mem (t _).2) hy, ?_⟩,
        add_neg_cancel_left _ _⟩
      have : (⟨-(t (φ ⟨y, hy⟩) : A) + y, L.add_mem (L.neg_mem (t _).2) hy⟩ : L) =
          -t (φ ⟨y, hy⟩) + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_neg, ht, neg_add_cancel]
    · rintro ⟨q, n, hn, rfl⟩
      obtain ⟨hnL, -⟩ := (hmemN n).1 hn
      exact L.add_mem (t q).2 hnL
  have hdisj : Pairwise (Function.onFun Disjoint fun q ↦ ((t q : L) : A) +ᵥ N) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨n, hn, rfl⟩ ⟨n', hn', h⟩
    obtain ⟨hnL, hn0⟩ := (hmemN n).1 hn
    obtain ⟨hnL', hn0'⟩ := (hmemN n').1 hn'
    apply hqq'
    have h' : (t q' : L) + ⟨n', hnL'⟩ = t q + ⟨n, hnL⟩ := Subtype.ext h
    have := congrArg φ h'
    rwa [map_add, map_add, hn0, hn0', add_zero, add_zero, ht, ht, eq_comm] at this
  have hmeas : MeasurableSet N := hker.measurableSet
  rw [hU, measure_iUnion hdisj fun q ↦ (hker.vadd _).measurableSet, tsum_fintype]
  simp only [measure_vadd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

variable {K : Type*} [Field K] [NumberField K]

def finiteSingleUnits (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (𝔸ᶠ[K])ˣ :=
  Units.map (IdeleGroup.finiteAdeleSingle v)

@[simp]
theorem coe_finiteSingleUnits (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) :
    ((finiteSingleUnits v z : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) = IdeleGroup.finiteAdeleSingle v (z : v.adicCompletion K) :=
  rfl

def finiteAdeleEval (x : HeightOneSpectrum (𝓞 K)) : 𝔸ᶠ[K] →* x.adicCompletion K :=
  RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) x

@[simp]
theorem finiteAdeleEval_apply (x : HeightOneSpectrum (𝓞 K)) (a : 𝔸ᶠ[K]) :
    finiteAdeleEval x a = a x :=
  rfl

open scoped Classical in

theorem coe_prod_finiteSingleUnits_apply (T : Finset (HeightOneSpectrum (𝓞 K)))
    (f : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (x : HeightOneSpectrum (𝓞 K)) :
    ((∏ v ∈ T, finiteSingleUnits v (f v) : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x =
      if x ∈ T then ((f x : (x.adicCompletion K)ˣ) : x.adicCompletion K) else 1 := by
  classical
  rw [Units.coe_prod]
  rw [← finiteAdeleEval_apply, map_prod]
  simp only [finiteAdeleEval_apply, coe_finiteSingleUnits]
  split_ifs with hx
  · rw [Finset.prod_eq_single_of_mem x hx fun b _ hbx ↦
      IdeleGroup.finiteAdeleSingle_apply_of_ne (Ne.symm hbx) _]
    exact IdeleGroup.finiteAdeleSingle_apply_self x _
  · exact Finset.prod_eq_one fun b hb ↦
      IdeleGroup.finiteAdeleSingle_apply_of_ne (fun h ↦ hx (by rw [h]; exact hb)) _

def IsIntegralUnitAt (u : (𝔸ᶠ[K])ˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (u : 𝔸ᶠ[K]) v ∈ v.adicCompletionIntegers K ∧
    ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v ∈ v.adicCompletionIntegers K

theorem finite_setOf_not_isIntegralUnitAt (u : (𝔸ᶠ[K])ˣ) :
    {v | ¬ IsIntegralUnitAt u v}.Finite :=
  Filter.eventually_cofinite.1 ((u : 𝔸ᶠ[K]).2.and ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]).2)

theorem units_mul_inv_apply (u : (𝔸ᶠ[K])ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : 𝔸ᶠ[K]) v * ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v = 1 := by
  exact congrArg (fun a : 𝔸ᶠ[K] ↦ a v) u.mul_inv

theorem norm_eq_one_of_isIntegralUnitAt {u : (𝔸ᶠ[K])ˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : IsIntegralUnitAt u v) : ‖(u : 𝔸ᶠ[K]) v‖ = 1 :=
  IdeleGroup.norm_eq_one_of_mul_eq_one (units_mul_inv_apply u v) h.1 h.2

theorem finite_mulSupport_nnnorm_units (u : (𝔸ᶠ[K])ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖₊).Finite := by
  refine (finite_setOf_not_isIntegralUnitAt u).subset fun v hv h ↦ hv ?_
  simpa [← NNReal.coe_inj] using norm_eq_one_of_isIntegralUnitAt h

variable (K) in
theorem finiteAdeleMeasure_integralFiniteAdeles_ne_zero :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ 0 := by
  rw [finiteAdeleMeasure_integralFiniteAdeles]
  exact ENNReal.coe_ne_zero.2 (inv_ne_zero (sqrt_discr_ne_zero K))

variable (K) in
theorem finiteAdeleMeasure_integralFiniteAdeles_ne_top :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ ∞ := by
  rw [finiteAdeleMeasure_integralFiniteAdeles]
  exact ENNReal.coe_ne_top

theorem smul_integralFiniteAdeles_of_forall {w : (𝔸ᶠ[K])ˣ} (hw : ∀ v, IsIntegralUnitAt w v) :
    w • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) = integralFiniteAdeles (𝓞 K) K := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe,
    SetLike.mem_coe]
  have h1 : ((w⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) ∈ integralFiniteAdeles (𝓞 K) K := fun v ↦ (hw v).2
  have h2 : (w : 𝔸ᶠ[K]) ∈ integralFiniteAdeles (𝓞 K) K := fun v ↦ (hw v).1
  constructor
  · intro h
    have := Subring.mul_mem _ h2 h
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this
  · exact fun h ↦ Subring.mul_mem _ h1 h

theorem distribHaarChar_eq_one_of_forall {w : (𝔸ᶠ[K])ˣ} (hw : ∀ v, IsIntegralUnitAt w v) :
    distribHaarChar 𝔸ᶠ[K] w = 1 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := finiteAdeleMeasure K)
    (finiteAdeleMeasure_integralFiniteAdeles_ne_zero K)
    (finiteAdeleMeasure_integralFiniteAdeles_ne_top K) ?_
  rw [smul_integralFiniteAdeles_of_forall hw, ENNReal.coe_one, one_mul]

theorem inv_mul_mem_adicCompletionIntegers_iff {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (x : v.adicCompletion K) :
    (ϖ : v.adicCompletion K)⁻¹ * x ∈ v.adicCompletionIntegers K ↔
      ∃ h : x ∈ v.adicCompletionIntegers K, (⟨x, h⟩ : v.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have hϖ0 : (ϖ : v.adicCompletion K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  constructor
  · intro h
    have hx : x = ϖ * ((ϖ : v.adicCompletion K)⁻¹ * x) := (mul_inv_cancel_left₀ hϖ0 x).symm
    have hxO : x ∈ v.adicCompletionIntegers K := by
      rw [hx]
      exact mul_mem ϖ.2 h
    refine ⟨hxO, Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩⟩
    change (ϖ : v.adicCompletion K)⁻¹ * x * ϖ = x
    rw [mul_comm, mul_inv_cancel_left₀ hϖ0]
  · rintro ⟨hx, hm⟩
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
    have hxr : x = r * ϖ := (congrArg Subtype.val hr).symm
    rw [hxr, mul_comm (r : v.adicCompletion K), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
    exact r.2

theorem mem_finiteSingleUnits_smul_iff (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ)
    (y : 𝔸ᶠ[K]) :
    y ∈ finiteSingleUnits v z • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) ↔
      (∀ w ≠ v, y w ∈ w.adicCompletionIntegers K) ∧
        (z : v.adicCompletion K)⁻¹ * y v ∈ v.adicCompletionIntegers K := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, ← map_inv, SetLike.mem_coe,
    mem_integralFiniteAdeles, coe_finiteSingleUnits]
  have hc : ∀ w, (IdeleGroup.finiteAdeleSingle v ((z⁻¹ : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) * y) w = IdeleGroup.finiteAdeleSingle v
        ((z⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w * y w := fun w ↦ rfl
  constructor
  · intro h
    refine ⟨fun w hw ↦ ?_, ?_⟩
    · have := h w
      rwa [hc, IdeleGroup.finiteAdeleSingle_apply_of_ne hw, one_mul] at this
    · have := h v
      rwa [hc, IdeleGroup.finiteAdeleSingle_apply_self, Units.val_inv_eq_inv_val] at this
  · rintro ⟨h1, h2⟩ w
    rw [hc]
    by_cases hw : w = v
    · subst hw
      rwa [IdeleGroup.finiteAdeleSingle_apply_self, Units.val_inv_eq_inv_val]
    · rw [IdeleGroup.finiteAdeleSingle_apply_of_ne hw, one_mul]
      exact h1 w hw

def residueAt (v : HeightOneSpectrum (𝓞 K)) :
    (integralFiniteAdeles (𝓞 K) K).toAddSubgroup →+
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) where
  toFun y := IsLocalRing.residue _ ⟨(y : 𝔸ᶠ[K]) v, y.2 v⟩
  map_zero' := by
    rw [← map_zero (IsLocalRing.residue (v.adicCompletionIntegers K))]
    rfl
  map_add' a b := by
    rw [← map_add]
    rfl

theorem residueAt_surjective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (residueAt (K := K) v) := by
  intro q
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective q
  have hr : IdeleGroup.finiteAdeleSingle v (r : v.adicCompletion K) ∈
      integralFiniteAdeles (𝓞 K) K := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [IdeleGroup.finiteAdeleSingle_apply_self]
      exact r.2
    · rw [IdeleGroup.finiteAdeleSingle_apply_of_ne hw]
      exact one_mem _
  refine ⟨⟨_, hr⟩, ?_⟩
  change IsLocalRing.residue (v.adicCompletionIntegers K)
    (⟨IdeleGroup.finiteAdeleSingle v (r : v.adicCompletion K) v, hr v⟩ :
      v.adicCompletionIntegers K) = IsLocalRing.residue _ r
  congr 1
  exact Subtype.ext (IdeleGroup.finiteAdeleSingle_apply_self v _)

theorem finiteSingleUnits_smul_eq_ker {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (hϖ0 : (ϖ : v.adicCompletion K) ≠ 0) :
    finiteSingleUnits v (Units.mk0 _ hϖ0) • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) =
      (((residueAt (K := K) v).ker.map (integralFiniteAdeles (𝓞 K) K).toAddSubgroup.subtype :
        AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) := by
  ext y
  rw [mem_finiteSingleUnits_smul_iff, Units.val_mk0, inv_mul_mem_adicCompletionIntegers_iff hϖ]
  simp only [AddSubgroup.coe_map, AddSubgroup.coe_subtype, Set.mem_image, SetLike.mem_coe,
    AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨h1, hv, hm⟩
    have hy : y ∈ integralFiniteAdeles (𝓞 K) K := fun w ↦ by
      by_cases hw : w = v
      · subst hw
        exact hv
      · exact h1 w hw
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    exact (IsLocalRing.residue_eq_zero_iff _).2 hm
  · rintro ⟨⟨y, hy⟩, h0, rfl⟩
    exact ⟨fun w _ ↦ hy w, hy v, (IsLocalRing.residue_eq_zero_iff _).1 h0⟩

theorem distribHaarChar_finiteSingleUnits_uniformizer {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (hϖ0 : (ϖ : v.adicCompletion K) ≠ 0) :
    distribHaarChar 𝔸ᶠ[K] (finiteSingleUnits v (Units.mk0 _ hϖ0)) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero v
  have hcount := measure_eq_card_mul_measure_ker (finiteAdeleMeasure K)
    (integralFiniteAdeles (𝓞 K) K).toAddSubgroup (residueAt v) (residueAt_surjective v)
    (by
      rw [← finiteSingleUnits_smul_eq_ker hϖ hϖ0]
      exact isOpen_integralFiniteAdeles.smul _)
  rw [natCard_residueField_adicCompletionIntegers] at hcount
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := finiteAdeleMeasure K)
    (finiteAdeleMeasure_integralFiniteAdeles_ne_zero K)
    (finiteAdeleMeasure_integralFiniteAdeles_ne_top K) ?_
  rw [finiteSingleUnits_smul_eq_ker hϖ hϖ0]
  change _ = _ * finiteAdeleMeasure K ((integralFiniteAdeles (𝓞 K) K).toAddSubgroup : Set 𝔸ᶠ[K])
  rw [hcount, ENNReal.coe_inv hN0, ENNReal.coe_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hN0) (ENNReal.natCast_ne_top _), one_mul]

def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom

theorem isIntegralUnitAt_finiteSingleUnits_integerUnits (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    IsIntegralUnitAt (finiteSingleUnits v (integerUnitsToUnits v u)) w := by
  rw [IsIntegralUnitAt, ← map_inv, coe_finiteSingleUnits, coe_finiteSingleUnits]
  by_cases hw : w = v
  · subst hw
    rw [IdeleGroup.finiteAdeleSingle_apply_self, IdeleGroup.finiteAdeleSingle_apply_self]
    exact ⟨(u : w.adicCompletionIntegers K).2, ((u⁻¹ : (w.adicCompletionIntegers K)ˣ) :
      w.adicCompletionIntegers K).2⟩
  · rw [IdeleGroup.finiteAdeleSingle_apply_of_ne hw, IdeleGroup.finiteAdeleSingle_apply_of_ne hw]
    exact ⟨one_mem _, one_mem _⟩

theorem nnnorm_integerUnitsToUnits (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((integerUnitsToUnits v u : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ = 1 := by
  have h := IdeleGroup.norm_eq_one_of_mul_eq_one (K := K) (v := v)
    (a := ((integerUnitsToUnits v u : (v.adicCompletion K)ˣ) : v.adicCompletion K))
    (b := ((integerUnitsToUnits v u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))
    (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
    (u : v.adicCompletionIntegers K).2 ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K).2
  exact NNReal.eq h

theorem distribHaarChar_finiteSingleUnits (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K)ˣ) :
    distribHaarChar 𝔸ᶠ[K] (finiteSingleUnits v z) = ‖(z : v.adicCompletion K)‖₊ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hϖ0 : (ϖ : v.adicCompletion K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hϖn : ‖(ϖ : v.adicCompletion K)‖₊ = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
    refine NNReal.eq ?_
    rw [coe_nnnorm, ← normalizedAbv_apply, normalizedAbv_of_irreducible v hϖ]
    push_cast
    rfl

  have hint : ∀ z : (v.adicCompletion K)ˣ, (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      distribHaarChar 𝔸ᶠ[K] (finiteSingleUnits v z) = ‖(z : v.adicCompletion K)‖₊ := by
    intro z hz
    have hz0 : (⟨z, hz⟩ : v.adicCompletionIntegers K) ≠ 0 := fun h ↦
      z.ne_zero (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hϖ
    have hzu : z = integerUnitsToUnits v u * Units.mk0 _ hϖ0 ^ n := by
      refine Units.ext ?_
      have := congrArg Subtype.val hu
      simpa [integerUnitsToUnits] using this
    rw [hzu, map_mul, map_mul, map_pow, map_pow,
      distribHaarChar_eq_one_of_forall (isIntegralUnitAt_finiteSingleUnits_integerUnits v u),
      distribHaarChar_finiteSingleUnits_uniformizer hϖ hϖ0, Units.val_mul, nnnorm_mul,
      nnnorm_integerUnitsToUnits, Units.val_pow_eq_pow_val, nnnorm_pow, Units.val_mk0, hϖn]
  rcases (v.adicCompletionIntegers K).mem_or_inv_mem (z : v.adicCompletion K) with hz | hz
  · exact hint z hz
  · have := hint z⁻¹ (by rwa [Units.val_inv_eq_inv_val])
    rw [map_inv, map_inv, Units.val_inv_eq_inv_val, nnnorm_inv, inv_inj] at this
    exact this

theorem distribHaarChar_finiteAdeleRing (u : (𝔸ᶠ[K])ˣ) :
    distribHaarChar 𝔸ᶠ[K] u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ := by
  classical
  set S := (finite_setOf_not_isIntegralUnitAt u).toFinset with hS
  have hmemS : ∀ x, x ∈ S ↔ ¬ IsIntegralUnitAt u x := fun x ↦ by simp [hS]
  let e : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ :=
    fun v ↦ Units.map (finiteAdeleEval v) u
  have he : ∀ v, ((e v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (u : 𝔸ᶠ[K]) v :=
    fun v ↦ rfl
  set P := ∏ v ∈ S, finiteSingleUnits v (e v) with hP
  have hPinv : P⁻¹ = ∏ v ∈ S, finiteSingleUnits v (e v)⁻¹ := by
    rw [hP, ← Finset.prod_inv_distrib]
    simp only [map_inv]
  set w := u * P⁻¹ with hw
  have hwint : ∀ x, IsIntegralUnitAt w x := by
    intro x
    have hwx : (w : 𝔸ᶠ[K]) x = (u : 𝔸ᶠ[K]) x * ((P⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x := rfl
    have hwx' : ((w⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x =
        ((P : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x * ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x := by
      rw [hw, mul_inv_rev, inv_inv]
      rfl
    rw [IsIntegralUnitAt, hwx', hwx, hPinv, coe_prod_finiteSingleUnits_apply, hP,
      coe_prod_finiteSingleUnits_apply]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx, Units.val_inv_eq_inv_val, he,
        mul_inv_cancel₀ (fun h ↦ by simpa [h] using units_mul_inv_apply u x),
        units_mul_inv_apply]
      exact ⟨one_mem _, one_mem _⟩
    · rw [if_neg hx, if_neg hx, mul_one, one_mul]
      exact not_not.1 ((hmemS x).not.1 hx)
  have hu : u = w * P := by rw [hw, inv_mul_cancel_right]
  have hχ : distribHaarChar 𝔸ᶠ[K] u = ∏ v ∈ S, ‖(u : 𝔸ᶠ[K]) v‖₊ := by
    conv_lhs => rw [hu]
    rw [map_mul, distribHaarChar_eq_one_of_forall hwint, one_mul, hP, map_prod]
    simp only [distribHaarChar_finiteSingleUnits, he]
  rw [hχ]
  refine (finprod_eq_prod_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖₊) (s := S) fun x hx ↦ ?_).symm
  rw [Finset.mem_coe, hmemS]
  intro h
  apply hx
  simpa [← NNReal.coe_inj] using norm_eq_one_of_isIntegralUnitAt h

theorem addHaar_smul_finiteAdeleRing (μ : Measure 𝔸ᶠ[K]) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : (𝔸ᶠ[K])ˣ) (E : Set 𝔸ᶠ[K]) :
    μ (u • E) = (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) * μ E := by
  rw [← distribHaarChar_finiteAdeleRing, distribHaarChar_mul]

theorem finiteAdeleMeasure_smul (u : (𝔸ᶠ[K])ˣ) (E : Set 𝔸ᶠ[K]) :
    finiteAdeleMeasure K (u • E) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) * finiteAdeleMeasure K E :=
  addHaar_smul_finiteAdeleRing _ u E

end

end GroundTheory.Global

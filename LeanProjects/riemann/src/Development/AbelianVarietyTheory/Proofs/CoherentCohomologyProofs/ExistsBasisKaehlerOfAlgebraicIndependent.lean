import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul

namespace GlobalTheory

open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing

section Alternating

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]

theorem alternating_smul_add_mem (ω : M [⋀^ι]→ₗ[R] N) (P : Submodule R N) (θ : M) (a : ι → R)
    (w : ι → M) (h₀ : ω w ∈ P) (h₁ : ∀ i, ω (Function.update w i θ) ∈ P) :
    ω (fun i => a i • θ + w i) ∈ P := by
  have e := ω.toMultilinearMap.map_add_univ (fun i => a i • θ) w
  change ω (fun i => a i • θ + w i) = ∑ s : Finset ι, ω (s.piecewise (fun i => a i • θ) w) at e
  rw [e]
  refine Submodule.sum_mem _ fun s _ => ?_
  have e₂ : s.piecewise (fun i => a i • θ) w
      = fun i => (s.piecewise a (fun _ => 1) i) • (s.piecewise (fun _ => θ) w i) := by
    funext i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [e₂, ω.map_smul_univ]
  refine P.smul_mem _ ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simpa using h₀
  by_cases hs : s = {i}
  · subst hs
    rw [Finset.piecewise_singleton]
    exact h₁ i
  · obtain ⟨j, hj, hji⟩ : ∃ j ∈ s, j ≠ i := by
      by_contra hc
      push Not at hc
      exact hs (Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, hc⟩)
    rw [ω.map_eq_zero_of_eq _ (i := j) (j := i) (by simp [hi, hj]) hji]
    exact P.zero_mem

theorem eq_lift_det_smul_ιMulti {n : ℕ} (b : Basis (Fin n) R M) (η : ⋀[R]^n M) :
    η = exteriorPower.alternatingMapLinearEquiv b.det η • exteriorPower.ιMulti R n b := by
  have key : (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M))
      = (exteriorPower.alternatingMapLinearEquiv b.det).smulRight (exteriorPower.ιMulti R n b) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    have e := alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti R n (M := M))
      (b.toMatrix v).transpose b
    rw [Matrix.det_transpose, ← Basis.det_apply] at e
    rw [← e]
    congr 1
    funext i
    simp [Basis.toMatrix_apply]
  exact congrArg (fun f : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M) => f η) key

end Alternating

section TwoInIdeal

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {p : ℕ}

theorem dWedge_mem_of_two_mem (t : A) (x : Fin p → A) {i j : Fin p} (hij : i ≠ j)
    (hi : t ∣ x i) (hj : t ∣ x j) :
    ∃ η : ⋀[A]^p Ω[A⁄R], dWedge R x = t • η := by
  classical
  let P : Submodule A (⋀[A]^p Ω[A⁄R]) := LinearMap.range (t • LinearMap.id)
  have hP : ∀ (v : Fin p → Ω[A⁄R]) (k : Fin p) (u : Ω[A⁄R]), v k = t • u →
      exteriorPower.ιMulti A p v ∈ P := by
    intro v k u h
    refine ⟨exteriorPower.ιMulti A p (Function.update v k u), ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← AlternatingMap.map_update_smul, ← h,
      Function.update_eq_self]
  have hx : ∀ k, ∃ (a : A) (w : Ω[A⁄R]), D R A (x k) = a • D R A t + w ∧
      (t ∣ x k → ∃ u, w = t • u) := by
    intro k
    by_cases hk : t ∣ x k
    · obtain ⟨c, hc⟩ := hk
      exact ⟨c, t • D R A c, by rw [hc, Derivation.leibniz, add_comm], fun _ => ⟨_, rfl⟩⟩
    · exact ⟨0, D R A (x k), by simp, fun h => absurd h hk⟩
  choose a w hw hw' using hx
  obtain ⟨ui, hui⟩ := hw' i hi
  obtain ⟨uj, huj⟩ := hw' j hj
  have : dWedge R x ∈ P := by
    rw [dWedge, funext hw]
    refine alternating_smul_add_mem _ P _ a w (hP w i ui hui) fun k => ?_
    by_cases hk : i = k
    · exact hP _ j uj (by rw [Function.update_of_ne (hk ▸ hij.symm), huj])
    · exact hP _ i ui (by rw [Function.update_of_ne hk, hui])
  obtain ⟨η, hη⟩ := this
  exact ⟨η, hη.symm⟩

end TwoInIdeal

section RegForms

variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)

noncomputable def formMap : (⋀[V]^p Ω[V⁄K]) →ₗ[V] (⋀[F]^p Ω[F⁄K]) :=
  exteriorPowerMapOver F p (KaehlerDifferential.map K K V F)

noncomputable def regForms : Submodule V (⋀[F]^p Ω[F⁄K]) :=
  LinearMap.range (formMap K V F p)

variable {V p}

@[simp] theorem formMap_ιMulti (v : Fin p → Ω[V⁄K]) :
    formMap K V F p (exteriorPower.ιMulti V p v)
      = exteriorPower.ιMulti F p (fun k => KaehlerDifferential.map K K V F (v k)) :=
  exteriorPowerMapOver_ιMulti _ _

theorem formMap_dWedge (x : Fin p → V) :
    formMap K V F p (dWedge K x) = dWedge K (fun k => algebraMap V F (x k)) := by
  simp [dWedge]

theorem ιMulti_mem_regForms (w : Fin p → Ω[F⁄K])
    (hw : ∀ k, w k ∈ LinearMap.range (KaehlerDifferential.map K K V F)) :
    exteriorPower.ιMulti F p w ∈ regForms K V F p := by
  choose v hv using hw
  exact ⟨exteriorPower.ιMulti V p v, by rw [formMap_ιMulti, funext hv]⟩

theorem dWedge_mem_regForms (x : Fin p → V) :
    dWedge K (fun k => algebraMap V F (x k)) ∈ regForms K V F p :=
  ⟨_, formMap_dWedge K F x⟩

theorem exists_dWedge_eq_smul_regForms (t : V) (x : Fin p → V) {i j : Fin p} (hij : i ≠ j)
    (hi : t ∣ x i) (hj : t ∣ x j) :
    ∃ η ∈ regForms K V F p, dWedge K (fun k => algebraMap V F (x k)) = t • η := by
  obtain ⟨η, hη⟩ := dWedge_mem_of_two_mem K t x hij hi hj
  exact ⟨_, ⟨η, rfl⟩, by rw [← formMap_dWedge, hη, map_smul]⟩

end RegForms

section LogWedge

variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}

noncomputable def dlogWedge (S : Finset (Fin p)) (x : Fin p → F) : ⋀[F]^p Ω[F⁄K] :=
  exteriorPower.ιMulti F p (fun k => if k ∈ S then (x k)⁻¹ • D K F (x k) else D K F (x k))

theorem dlogWedge_eq_smul (S : Finset (Fin p)) (x : Fin p → F) :
    dlogWedge K S x = (∏ k ∈ S, x k)⁻¹ • dWedge K x := by
  have : (fun k => if k ∈ S then (x k)⁻¹ • D K F (x k) else D K F (x k))
      = fun k => (if k ∈ S then (x k)⁻¹ else 1) • D K F (x k) := by
    funext k
    split_ifs <;> simp
  rw [dlogWedge, this, AlternatingMap.map_smul_univ, dWedge]
  congr 1
  simp [Finset.prod_ite_mem]

@[simp] theorem dlogWedge_empty (x : Fin p → F) : dlogWedge K ∅ x = dWedge K x := by
  simp [dlogWedge_eq_smul]

theorem dlog_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y)⁻¹ • D K F (x * y) = x⁻¹ • D K F x + y⁻¹ • D K F y := by
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, add_comm]
  congr 2 <;> field_simp

theorem dlog_zpow {x : F} (hx : x ≠ 0) (m : ℤ) :
    (x ^ m)⁻¹ • D K F (x ^ m) = m • x⁻¹ • D K F x := by
  rw [Derivation.leibniz_zpow, smul_comm, smul_smul]
  congr 2
  rw [zpow_sub_one₀ hx, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero m hx), one_mul]

variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]

theorem dlog_unit_mem_range (u : Vˣ) :
    (algebraMap V F u)⁻¹ • D K F (algebraMap V F u)
      ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by
  refine ⟨((u⁻¹ : Vˣ) : V) • D K V u, ?_⟩
  rw [map_smul, map_D, ← map_units_inv, algebraMap_smul]

theorem dlogWedge_mem_regForms (S : Finset (Fin p)) (x : Fin p → V)
    (hS : ∀ k ∈ S, IsUnit (x k)) :
    dlogWedge K S (fun k => algebraMap V F (x k)) ∈ regForms K V F p := by
  refine ιMulti_mem_regForms K F _ fun k => ?_
  split_ifs with hk
  · obtain ⟨u, hu⟩ := hS k hk
    simp only [← hu]
    exact dlog_unit_mem_range K u
  · exact ⟨D K V (x k), map_D ..⟩

theorem smul_dlogWedge_mem_regForms (t : V) (ht : algebraMap V F t ≠ 0) (S : Finset (Fin p))
    (x : Fin p → F) (hS : ∀ k ∈ S, ∃ (m : ℤ) (u : Vˣ), x k = algebraMap V F u * algebraMap V F t ^ m)
    (hS' : ∀ k ∉ S, x k ∈ Set.range (algebraMap V F)) :
    t • dlogWedge K S x ∈ regForms K V F p := by
  classical
  let θ : Ω[F⁄K] := (algebraMap V F t)⁻¹ • D K F (algebraMap V F t)
  have hθ : t • θ ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by
    refine ⟨D K V t, ?_⟩
    rw [map_D, ← algebraMap_smul F t, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hx : ∀ k, ∃ (a : V) (w : Ω[F⁄K]),
      (if k ∈ S then (x k)⁻¹ • D K F (x k) else D K F (x k)) = a • θ + w ∧
        w ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by
    intro k
    split_ifs with hk
    · obtain ⟨m, u, h⟩ := hS k hk
      refine ⟨m, _, ?_, dlog_unit_mem_range K u⟩
      rw [h, dlog_mul K ((u.isUnit.map (algebraMap V F)).ne_zero) (zpow_ne_zero m ht),
        dlog_zpow K ht, add_comm, Int.cast_smul_eq_zsmul]
    · obtain ⟨y, hy⟩ := hS' k hk
      exact ⟨0, _, by rw [zero_smul, zero_add], D K V y, by rw [map_D, hy]⟩
  choose a w hw hw' using hx
  let P : Submodule V (⋀[F]^p Ω[F⁄K]) := (regForms K V F p).comap (t • LinearMap.id)
  have : altRestrictScalars V (exteriorPower.ιMulti F p) (fun k => a k • θ + w k) ∈ P := by
    refine alternating_smul_add_mem _ P θ a w ?_ fun k => ?_
    · exact (regForms K V F p).smul_mem t (ιMulti_mem_regForms K F w hw')
    · change t • altRestrictScalars V (exteriorPower.ιMulti F p) (Function.update w k θ)
        ∈ regForms K V F p
      rw [← AlternatingMap.map_update_smul]
      refine ιMulti_mem_regForms K F _ fun l => ?_
      by_cases hl : l = k
      · subst hl
        rwa [Function.update_self]
      · rw [Function.update_of_ne hl]
        exact hw' l
  rw [dlogWedge, funext hw]
  exact this

end LogWedge

section Order

variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]

open Classical in

noncomputable def ordTop_vw (f : F) : WithTop ℤ :=
  if f = 0 then ⊤ else (WithZero.log (Ring.ordFrac V f) : ℤ)

@[simp] theorem ordTop_vw_zero : ordTop_vw V (0 : F) = ⊤ := if_pos rfl

theorem ordTop_vw_of_ne_zero {f : F} (hf : f ≠ 0) :
    ordTop_vw V f = (WithZero.log (Ring.ordFrac V f) : ℤ) := if_neg hf

theorem ordTop_vw_eq_top_iff {f : F} : ordTop_vw V f = ⊤ ↔ f = 0 := by
  by_cases hf : f = 0
  · simp [hf]
  · simp [hf, ordTop_vw_of_ne_zero V hf]

theorem ordTop_vw_mul (f g : F) : ordTop_vw V (f * g) = ordTop_vw V f + ordTop_vw V g := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  rw [ordTop_vw_of_ne_zero V hf, ordTop_vw_of_ne_zero V hg, ordTop_vw_of_ne_zero V (mul_ne_zero hf hg),
    map_mul, WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg), WithTop.coe_add]

variable {V}

theorem ordTop_vw_unit_mul_zpow {t : V} (ht : Irreducible t) (u : Vˣ) (m : ℤ) :
    ordTop_vw V (algebraMap V F u * algebraMap V F t ^ m) = m := by
  have h₀ : algebraMap V F t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V F)).mpr ht.ne_zero
  rw [ordTop_vw_of_ne_zero V
      (mul_ne_zero (u.isUnit.map (algebraMap V F)).ne_zero (zpow_ne_zero m h₀)),
    map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible ht, one_mul,
    WithZero.log_zpow, WithZero.log_exp]
  simp

theorem exists_eq_unit_mul_zpow {t : V} (ht : Irreducible t) {f : F} (hf : f ≠ 0) :
    ∃ (m : ℤ) (u : Vˣ), f = algebraMap V F u * algebraMap V F t ^ m := by
  obtain ⟨m, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible ht hf
  exact ⟨m, u, by rw [h, Units.smul_def, Algebra.smul_def]⟩

theorem le_ordTop_vw_iff {t : V} (ht : Irreducible t) (m : ℤ) (f : F) :
    (m : WithTop ℤ) ≤ ordTop_vw V f ↔ ∃ a : V, f = algebraMap V F t ^ m * algebraMap V F a := by
  have h₀ : algebraMap V F t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V F)).mpr ht.ne_zero
  constructor
  · intro h
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    obtain ⟨k, u, rfl⟩ := exists_eq_unit_mul_zpow ht hf
    rw [ordTop_vw_unit_mul_zpow ht, WithTop.coe_le_coe] at h
    obtain ⟨d, rfl⟩ := Int.le.dest h
    exact ⟨u * t ^ d, by rw [zpow_add₀ h₀, map_mul, map_pow, zpow_natCast]; ring⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨d, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha ht
    have : algebraMap V F t ^ m * algebraMap V F (u * t ^ d)
        = algebraMap V F u * algebraMap V F t ^ (m + d) := by
      rw [zpow_add₀ h₀, map_mul, map_pow, zpow_natCast]; ring
    rw [this, ordTop_vw_unit_mul_zpow ht, WithTop.coe_le_coe]
    omega

variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}

noncomputable def fracKaehlerBasis (b : Basis (Fin n) V Ω[V⁄K]) : Basis (Fin n) F Ω[F⁄K] :=
  b.ofIsLocalizedModule F V⁰ (KaehlerDifferential.map K K V F)

omit [IsDomain V] [IsDiscreteValuationRing V] in
@[simp] theorem fracKaehlerBasis_apply (b : Basis (Fin n) V Ω[V⁄K]) (k : Fin n) :
    fracKaehlerBasis F b k = KaehlerDifferential.map K K V F (b k) :=
  b.ofIsLocalizedModule_apply F V⁰ _ k

noncomputable def topFormGen (b : Basis (Fin n) V Ω[V⁄K]) : ⋀[F]^n Ω[F⁄K] :=
  formMap K V F n (exteriorPower.ιMulti V n b)

noncomputable def topFormCoeff (b : Basis (Fin n) V Ω[V⁄K]) : (⋀[F]^n Ω[F⁄K]) →ₗ[F] F :=
  exteriorPower.alternatingMapLinearEquiv (fracKaehlerBasis F b).det

noncomputable def topFormOrd_vw (b : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]) : WithTop ℤ :=
  ordTop_vw V (topFormCoeff F b ω)

variable {F} (b : Basis (Fin n) V Ω[V⁄K])

omit [IsDomain V] [IsDiscreteValuationRing V] in
theorem topFormGen_eq : topFormGen F b = exteriorPower.ιMulti F n (fracKaehlerBasis F b) := by
  rw [topFormGen, formMap_ιMulti]
  congr 1
  funext k
  simp

omit [IsDomain V] [IsDiscreteValuationRing V] in
@[simp] theorem topFormCoeff_topFormGen : topFormCoeff F b (topFormGen F b) = 1 := by
  rw [topFormGen_eq, topFormCoeff, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_self]

omit [IsDomain V] [IsDiscreteValuationRing V] in

theorem topFormCoeff_smul_topFormGen (ω : ⋀[F]^n Ω[F⁄K]) :
    topFormCoeff F b ω • topFormGen F b = ω := by
  rw [topFormGen_eq]
  exact (eq_lift_det_smul_ιMulti _ ω).symm

omit [IsDomain V] [IsDiscreteValuationRing V] in
theorem topFormGen_ne_zero : topFormGen F b ≠ 0 := by
  intro h
  have := topFormCoeff_topFormGen (F := F) b
  rw [h, map_zero] at this
  exact zero_ne_one this

omit [IsDomain V] [IsDiscreteValuationRing V] in

theorem mem_regForms_iff (ω : ⋀[F]^n Ω[F⁄K]) :
    ω ∈ regForms K V F n ↔ ∃ a : V, ω = a • topFormGen F b := by
  constructor
  · rintro ⟨η, rfl⟩
    refine ⟨exteriorPower.alternatingMapLinearEquiv b.det η, ?_⟩
    rw [topFormGen, ← map_smul, ← eq_lift_det_smul_ιMulti]
  · rintro ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩

theorem topFormOrd_vw_smul_topFormGen (f : F) :
    topFormOrd_vw F b (f • topFormGen F b) = ordTop_vw V f := by
  simp [topFormOrd_vw]

theorem topFormOrd_vw_smul (f : F) (ω : ⋀[F]^n Ω[F⁄K]) :
    topFormOrd_vw F b (f • ω) = ordTop_vw V f + topFormOrd_vw F b ω := by
  simp [topFormOrd_vw, ordTop_vw_mul]

theorem topFormOrd_vw_eq_top_iff (ω : ⋀[F]^n Ω[F⁄K]) : topFormOrd_vw F b ω = ⊤ ↔ ω = 0 := by
  rw [topFormOrd_vw, ordTop_vw_eq_top_iff]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  rw [← topFormCoeff_smul_topFormGen b ω, h, zero_smul]

theorem le_topFormOrd_vw_iff {t : V} (ht : Irreducible t) (m : ℤ) (ω : ⋀[F]^n Ω[F⁄K]) :
    (m : WithTop ℤ) ≤ topFormOrd_vw F b ω ↔
      ∃ η ∈ regForms K V F n, ω = algebraMap V F t ^ m • η := by
  rw [topFormOrd_vw, le_ordTop_vw_iff ht]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨_, (mem_regForms_iff b _).mpr ⟨a, rfl⟩, ?_⟩
    rw [← algebraMap_smul F a, smul_smul, ← ha, topFormCoeff_smul_topFormGen]
  · rintro ⟨η, hη, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_regForms_iff b η).mp hη
    exact ⟨a, by rw [← algebraMap_smul F a, smul_smul, map_smul, topFormCoeff_topFormGen,
      smul_eq_mul, mul_one]⟩

theorem topFormOrd_vw_nonneg_iff (ω : ⋀[F]^n Ω[F⁄K]) :
    0 ≤ topFormOrd_vw F b ω ↔ ω ∈ regForms K V F n := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  simpa using le_topFormOrd_vw_iff b ht 0 ω

theorem topFormOrd_vw_eq (b' : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]) :
    topFormOrd_vw F b ω = topFormOrd_vw F b' ω := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ c c' : Basis (Fin n) V Ω[V⁄K], topFormOrd_vw F c ω ≤ topFormOrd_vw F c' ω := by
    intro c c'
    by_cases h : topFormOrd_vw F c ω = ⊤
    · rw [(topFormOrd_vw_eq_top_iff c' ω).mpr ((topFormOrd_vw_eq_top_iff c ω).mp h)]
      exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h
      rw [← hm, le_topFormOrd_vw_iff c' ht, ← le_topFormOrd_vw_iff c ht, hm]
  exact le_antisymm (key b b') (key b' b)

theorem topFormOrd_vw_topFormGen (b' : Basis (Fin n) V Ω[V⁄K]) :
    topFormOrd_vw F b (topFormGen F b') = 0 := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  rw [topFormOrd_vw_eq b b', topFormOrd_vw, topFormCoeff_topFormGen]
  simpa using ordTop_vw_unit_mul_zpow (F := F) ht 1 0

theorem topFormOrd_vw_dWedge_nonneg (x : Fin n → V) :
    0 ≤ topFormOrd_vw F b (dWedge K fun k => algebraMap V F (x k)) :=
  (topFormOrd_vw_nonneg_iff b _).mpr (dWedge_mem_regForms K F x)

theorem one_le_topFormOrd_vw_dWedge (x : Fin n → V) {i j : Fin n} (hij : i ≠ j)
    (hi : x i ∈ maximalIdeal V) (hj : x j ∈ maximalIdeal V) :
    1 ≤ topFormOrd_vw F b (dWedge K fun k => algebraMap V F (x k)) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  rw [ht.maximalIdeal_eq, Ideal.mem_span_singleton] at hi hj
  obtain ⟨η, hη, h⟩ := exists_dWedge_eq_smul_regForms K F t x hij hi hj
  exact (le_topFormOrd_vw_iff b ht 1 _).mpr ⟨η, hη, by rw [h, zpow_one, algebraMap_smul]⟩

theorem neg_one_le_topFormOrd_vw_dlogWedge (S : Finset (Fin n)) (x : Fin n → F)
    (hS : ∀ k ∈ S, x k ≠ 0) (hS' : ∀ k ∉ S, x k ∈ Set.range (algebraMap V F)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ topFormOrd_vw F b (dlogWedge K S x) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h₀ : algebraMap V F t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V F)).mpr ht.ne_zero
  refine (le_topFormOrd_vw_iff b ht (-1) _).mpr ⟨_, smul_dlogWedge_mem_regForms K t h₀ S x
    (fun k hk => exists_eq_unit_mul_zpow ht (hS k hk)) hS', ?_⟩
  rw [← algebraMap_smul F t, smul_smul, zpow_neg_one, inv_mul_cancel₀ h₀, one_smul]

theorem topFormOrd_vw_dlogWedge_nonneg (S : Finset (Fin n)) (x : Fin n → V)
    (hS : ∀ k ∈ S, IsUnit (x k)) :
    0 ≤ topFormOrd_vw F b (dlogWedge K S fun k => algebraMap V F (x k)) :=
  (topFormOrd_vw_nonneg_iff b _).mpr (dlogWedge_mem_regForms K S x hS)

theorem topFormOrd_vw_dWedge_basis (z : Fin n → V) (c : Basis (Fin n) V Ω[V⁄K])
    (hc : ∀ k, c k = D K V (z k)) :
    topFormOrd_vw F b (dWedge K fun k => algebraMap V F (z k)) = 0 := by
  rw [← topFormOrd_vw_topFormGen (F := F) b c, ← formMap_dWedge, topFormGen, dWedge, ← funext hc]

theorem topFormOrd_vw_dlogWedge_basis (z : Fin n → V) (c : Basis (Fin n) V Ω[V⁄K])
    (hc : ∀ k, c k = D K V (z k)) {i : Fin n} (hi : Irreducible (z i)) :
    topFormOrd_vw F b (dlogWedge K {i} fun k => algebraMap V F (z k)) = ((-1 : ℤ) : WithTop ℤ) := by
  rw [dlogWedge_eq_smul, topFormOrd_vw_smul, topFormOrd_vw_dWedge_basis b z c hc, add_zero,
    Finset.prod_singleton]
  simpa using ordTop_vw_unit_mul_zpow (F := F) hi 1 (-1)

end Order

section Existence

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem exists_basis_kaehler_of_algebraicIndependent {K F ι : Type*} [Field K] [Field F]
    [Algebra K F] {v : ι → F} (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F] :
    ∃ b : Basis ι F Ω[F⁄K], ∀ i, b i = D K F (v i) := by
  let P := MvPolynomial ι K
  let A := Algebra.adjoin K (Set.range v)
  let L := IntermediateField.adjoin K (Set.range v)
  letI : Algebra P A := hv.aevalEquiv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K P A :=
    .of_algebraMap_eq fun r => (hv.aevalEquiv.commutes r).symm
  haveI : Algebra.FormallyEtale P A :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable _ F
  haveI : Algebra.FormallyEtale A F := .comp A L F
  let b₁ : Basis ι A Ω[A⁄K] :=
    ((mvPolynomialBasis K ι).baseChange A).map (tensorKaehlerEquivOfFormallyEtale K P A)
  refine ⟨(b₁.baseChange F).map (tensorKaehlerEquivOfFormallyEtale K A F), fun i => ?_⟩
  simp only [b₁, Basis.map_apply, Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
  have h : algebraMap A F (algebraMap P A (MvPolynomial.X i)) = v i := by
    change algebraMap A F (hv.aevalEquiv (MvPolynomial.X i)) = v i
    rw [hv.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  rw [← h, ← map_D K K A F, ← map_D K K P A]
  exact congrArg _ ((mapBaseChange_tmul K P A 1 _).trans (one_smul _ _))

theorem rank_kaehler_eq_trdeg (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] : Module.rank F Ω[F⁄K] = Algebra.trdeg K F := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F := by
    convert! H <;> simp
  obtain ⟨b, -⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
  rw [← hs.cardinalMk_eq_trdeg, ← b.mk_eq_rank'']

variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]

theorem one_tmul_D_ne_zero {t : V} (ht : Irreducible t) :
    (1 : ResidueField V) ⊗ₜ[V] D K V t ≠ 0 := by
  have hs : Function.Surjective (algebraMap V (ResidueField V)) := residue_surjective
  have : Algebra.EssFiniteType K (ResidueField V) := .comp K V _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := K) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap V (ResidueField V)) = Ideal.span {t} :=
    ker_residue.trans ht.maximalIdeal_eq
  have hmem : t ∈ RingHom.ker (algebraMap V (ResidueField V)) :=
    hker ▸ Ideal.mem_span_singleton_self t
  intro h
  have h₁ : (RingHom.ker (algebraMap V (ResidueField V))).toCotangent ⟨t, hmem⟩ = 0 := by
    apply hinj
    rw [kerCotangentToTensor_toCotangent, map_zero]
    exact h
  have h₂ : t ∈ RingHom.ker (algebraMap V (ResidueField V)) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp h₁
  rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h₂
  obtain ⟨c, hc⟩ := h₂
  have : t * 1 = t * (t * c) := by rw [mul_one, ← mul_assoc, ← sq]; exact hc
  exact ht.not_isUnit (IsUnit.of_mul_eq_one c (mul_left_cancel₀ ht.ne_zero this).symm)

theorem exists_basis_kaehler_uniformiser {t : V} (ht : Irreducible t) :
    ∃ (m : ℕ) (z : Fin (m + 1) → V) (b : Basis (Fin (m + 1)) V Ω[V⁄K]),
      z 0 = t ∧ ∀ k, b k = D K V (z k) := by
  classical
  let κ := ResidueField V
  let f : V → κ ⊗[V] Ω[V⁄K] := TensorProduct.mk V κ Ω[V⁄K] 1 ∘ D K V
  have hspan : Submodule.span κ (Set.range f) = ⊤ := by
    have := (map_tensorProduct_mk_eq_top (N := Submodule.span V (Set.range (D K V)))).mpr
      (span_range_derivation K V)
    rw [← Submodule.span_image, ← Set.range_comp, eq_top_iff, ← SetLike.coe_subset_coe,
      Submodule.top_coe] at this
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  have h₁ : LinearIndepOn κ f {t} := LinearIndepOn.singleton (one_tmul_D_ne_zero K ht)
  obtain ⟨T, -, htT, hT, hli⟩ := exists_linearIndepOn_extension h₁ (Set.subset_univ _)
  have hT' : Submodule.span κ (f '' T) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le, ← Set.image_univ]
    exact hT
  have hfin : Finite T := hli.linearIndependent.finite
  have hne : Nonempty T := ⟨⟨t, htT rfl⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card T = m + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  let e₀ : Fin (m + 1) ≃ T := (Finite.equivFinOfCardEq hm).symm
  let e : Fin (m + 1) ≃ T := (Equiv.swap 0 (e₀.symm ⟨t, htT rfl⟩)).trans e₀
  have : Module.FinitePresentation V Ω[V⁄K] := Module.finitePresentation_of_finite V _
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := V)
    (fun k => D K V (e k : V)) (hli.linearIndependent.comp e e.injective)
    (by
      rw [← hT']
      congr 1
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e k, (e k).2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e.symm ⟨x, hx⟩, by simp [f]⟩)
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)
  exact ⟨m, fun k => e k, b, by simp [e], hb⟩

variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]

omit [IsDomain V] [IsDiscreteValuationRing V] [Algebra.FormallySmooth K V] in

theorem trdeg_eq_of_basis_kaehler {n : ℕ} (b : Basis (Fin n) V Ω[V⁄K]) :
    Algebra.trdeg K F = n := by
  have : Algebra.EssFiniteType V F := .of_isLocalization F V⁰
  have : Algebra.EssFiniteType K F := .comp K V F
  rw [← rank_kaehler_eq_trdeg, rank_eq_card_basis (fracKaehlerBasis F b), Fintype.card_fin]

theorem exists_basis_kaehler_of_trdeg {n : ℕ} (hn : Algebra.trdeg K F = n) {t : V}
    (ht : Irreducible t) :
    ∃ (h : 0 < n) (z : Fin n → V) (b : Basis (Fin n) V Ω[V⁄K]),
      z ⟨0, h⟩ = t ∧ ∀ k, b k = D K V (z k) := by
  obtain ⟨m, z, b, h₀, hb⟩ := exists_basis_kaehler_uniformiser K ht
  have := trdeg_eq_of_basis_kaehler K F b
  rw [hn, Nat.cast_inj] at this
  subst this
  exact ⟨m.succ_pos, z, b, h₀, hb⟩

variable (V) in

theorem trdeg_residueField_of_trdeg {n : ℕ} (hn : Algebra.trdeg K F = n) :
    Algebra.trdeg K (ResidueField V) = (n - 1 : ℕ) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨h, z, b, -, -⟩ := exists_basis_kaehler_of_trdeg K F hn ht
  let κ := ResidueField V
  have hs : Function.Surjective (algebraMap V κ) := residue_surjective
  have : Algebra.EssFiniteType K κ := .comp K V _
  have hker : RingHom.ker (algebraMap V κ) = Ideal.span {t} :=
    ker_residue.trans ht.maximalIdeal_eq
  have hk : LinearMap.ker (mapBaseChange K V κ) = Submodule.span κ {(1 : κ) ⊗ₜ[V] D K V t} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange K V κ hs y).mp hy
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
      rw [kerCotangentToTensor_toCotangent]
      rw [hker, Ideal.mem_span_singleton'] at hx
      obtain ⟨a, rfl⟩ := hx
      have ht₀ : algebraMap V κ t = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact Ideal.mem_span_singleton_self t
      change (1 : κ) ⊗ₜ[V] D K V (a * t) ∈ _
      rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul, ← algebraMap_smul κ t, ht₀, zero_smul, add_zero,
        ← algebraMap_smul κ a]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        mapBaseChange_tmul, map_D]
      have ht₀ : algebraMap V κ t = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact Ideal.mem_span_singleton_self t
      rw [ht₀, map_zero, smul_zero]
  have h₂ := LinearMap.finrank_range_add_finrank_ker (mapBaseChange K V κ)
  rw [hk, finrank_span_singleton (one_tmul_D_ne_zero K ht),
    LinearMap.range_eq_top.mpr (mapBaseChange_surjective K V κ hs), finrank_top,
    finrank_eq_card_basis (b.baseChange κ), Fintype.card_fin] at h₂
  rw [← rank_kaehler_eq_trdeg, ← finrank_eq_rank, ← h₂, Nat.add_sub_cancel]

end Existence

section Main

theorem topFormOrd_vw_properties (K V F : Type*) [Field K] [CharZero K] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
    [Algebra.FormallySmooth K V] [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
    [IsScalarTower K V F] {n : ℕ} (hn : Algebra.trdeg K F = n) :
    Algebra.trdeg K (ResidueField V) = (n - 1 : ℕ) ∧
    (∀ t : V, Irreducible t → ∃ (h : 0 < n) (z : Fin n → V) (b : Basis (Fin n) V Ω[V⁄K]),
      z ⟨0, h⟩ = t ∧ ∀ k, b k = D K V (z k)) ∧
    Nonempty (Basis (Fin n) V Ω[V⁄K]) ∧
    ∀ b : Basis (Fin n) V Ω[V⁄K],
      (∀ (b' : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]),
        topFormOrd_vw F b ω = topFormOrd_vw F b' ω) ∧
      (∀ ω : ⋀[F]^n Ω[F⁄K], ∃! f : F, ω = f • topFormGen F b) ∧
      (∀ f : F, topFormOrd_vw F b (f • topFormGen F b) = ordTop_vw V f) ∧
      (∀ x : Fin n → V, 0 ≤ topFormOrd_vw F b (dWedge K fun i => algebraMap V F (x i))) ∧
      (∀ (x : Fin n → V) (i j : Fin n), i ≠ j → x i ∈ maximalIdeal V → x j ∈ maximalIdeal V →
        1 ≤ topFormOrd_vw F b (dWedge K fun i => algebraMap V F (x i))) ∧
      (∀ (k : ℕ) (x : Fin n → F), (∀ i : Fin n, i.val < k → x i ≠ 0) →
        (∀ i : Fin n, k ≤ i.val → x i ∈ Set.range (algebraMap V F)) →
        ((-1 : ℤ) : WithTop ℤ) ≤ topFormOrd_vw F b (exteriorPower.ιMulti F n fun i =>
          if i.val < k then (x i)⁻¹ • D K F (x i) else D K F (x i))) ∧
      (∀ (k : ℕ) (x : Fin n → V), (∀ i : Fin n, i.val < k → IsUnit (x i)) →
        0 ≤ topFormOrd_vw F b (exteriorPower.ιMulti F n fun i =>
          if i.val < k then (algebraMap V F (x i))⁻¹ • D K F (algebraMap V F (x i))
          else D K F (algebraMap V F (x i)))) := by
  refine ⟨trdeg_residueField_of_trdeg K V F hn,
    fun t ht => exists_basis_kaehler_of_trdeg K F hn ht, ?_, fun b =>
    ⟨topFormOrd_vw_eq b, fun ω => ⟨_, (topFormCoeff_smul_topFormGen b ω).symm, ?_⟩,
      topFormOrd_vw_smul_topFormGen b, topFormOrd_vw_dWedge_nonneg b,
      fun x i j hij hi hj => one_le_topFormOrd_vw_dWedge b x hij hi hj, ?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨-, -, b, -, -⟩ := exists_basis_kaehler_of_trdeg K F hn ht
    exact ⟨b⟩
  · rintro f rfl
    simp
  · intro k x h₁ h₂
    have := neg_one_le_topFormOrd_vw_dlogWedge b (Finset.univ.filter fun i => i.val < k) x
      (fun i hi => h₁ i (by simpa using hi)) (fun i hi => h₂ i (by simpa using hi))
    simpa only [dlogWedge, Finset.mem_filter, Finset.mem_univ, true_and] using this
  · intro k x h₁
    have := topFormOrd_vw_dlogWedge_nonneg (F := F) b (Finset.univ.filter fun i => i.val < k) x
      (fun i hi => h₁ i (by simpa using hi))
    simpa only [dlogWedge, Finset.mem_filter, Finset.mem_univ, true_and] using this

end Main

section Example

open Polynomial

variable (K : Type*) [Field K]

theorem exists_smooth_discreteValuationRing :
    ∃ (V : Subalgebra K (RatFunc K)) (_ : IsDiscreteValuationRing V),
      Algebra.EssFiniteType K V ∧ Algebra.FormallySmooth K V ∧ IsFractionRing V (RatFunc K) ∧
        Algebra.trdeg K (RatFunc K) = (1 : ℕ) := by
  let 𝔭 : Ideal K[X] := Ideal.span {X}
  haveI : 𝔭.IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  have h𝔭 : 𝔭 ≠ ⊥ := by simp [𝔭]
  let W : Subalgebra K[X] (RatFunc K) :=
    Localization.subalgebra.ofField (RatFunc K) 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime W 𝔭 := Localization.subalgebra.isLocalization_ofField ..
  haveI h₁ : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain K[X] h𝔭 W
  haveI : Algebra.EssFiniteType K[X] W := .of_isLocalization W 𝔭.primeCompl
  haveI : Algebra.FormallySmooth K[X] W := .of_isLocalization 𝔭.primeCompl
  have h₂ : Algebra.EssFiniteType K W := .comp K K[X] W
  have h₃ : Algebra.FormallySmooth K W := .comp K K[X] W
  have h₄ : IsFractionRing W (RatFunc K) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl W (RatFunc K)
  refine ⟨W.restrictScalars K, h₁, h₂, h₃, h₄, ?_⟩
  haveI : Algebra.IsAlgebraic K[X] (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors K[X])
  rw [← trdeg_add_eq K K[X], trdeg_eq_zero (R := K[X]) (A := RatFunc K)]
  simp

end Example

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField

namespace GlobalTheory.DualIndex

theorem relIndex_dvd_of_le_right {G : Type*} [AddCommGroup G] (H K K' : AddSubgroup G)
    (h1 : H ≤ K') (h2 : K ≤ K') : H.relIndex K ∣ H.relIndex K' := by
  rw [← AddSubgroup.relIndex_sup_left K H,
    ← AddSubgroup.relIndex_mul_relIndex H (H ⊔ K) K' le_sup_left (sup_le h1 h2)]
  exact dvd_mul_right _ _

theorem absNorm_eq_index' {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem inv_relIndex_dvd {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (K : AddSubgroup F) (hK : ∀ f ∈ K, ∀ i ∈ I, i • f ∈ (1 : Submodule (𝓞 F) F)) :
    (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex K ∣ I.toAddSubgroup.index := by
  by_cases hI : I = ⊥
  · rw [← absNorm_eq_index', hI]; simp
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haI)
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := FaithfulSMul.algebraMap_injective _ _
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha
  have hmul : Function.Injective (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a)) :=
    mul_right_injective₀ haF
  have hJ0 : Ideal.absNorm J ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact ha hJ
  have hle : (Ideal.span {a}).toAddSubgroup ≤ J.toAddSubgroup := by
    have : Ideal.span {a} ≤ J := Ideal.dvd_iff_le.1 ⟨I, by rw [hJ, mul_comm]⟩
    exact this
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex J.toAddSubgroup = I.toAddSubgroup.index := by
    have := AddSubgroup.relIndex_mul_index hle
    rw [← absNorm_eq_index', ← absNorm_eq_index', hJ, map_mul] at this
    rw [← absNorm_eq_index', hJ]
    exact mul_right_cancel₀ hJ0 this
  rw [← h1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hmul,
    ← AddSubgroup.relIndex_map_map_of_injective (f := (algebraMap (𝓞 F) F).toAddMonoidHom)
      (Ideal.span {a}).toAddSubgroup _ hinj]
  have e : AddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a))
      (1 : Submodule (𝓞 F) F).toAddSubgroup =
      AddSubgroup.map (algebraMap (𝓞 F) F).toAddMonoidHom (Ideal.span {a}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c * a, ⟨c, rfl⟩, by simp [mul_comm]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, by simp [mul_comm]⟩
  rw [e]
  refine relIndex_dvd_of_le_right _ _ _ (AddSubgroup.map_mono hle) ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hK f hf a haI)
  refine ⟨c, ?_, by simpa [Algebra.smul_def] using hc⟩
  have : I * Ideal.span {c} ≤ I * J := by
    rw [← hJ, Ideal.mul_le]
    intro i hi s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (hK f hf i hi)
    refine Ideal.mem_span_singleton'.2 ⟨t * d, hinj ?_⟩
    simp only [map_mul, hc, hd, Algebra.smul_def]
    ring
  have h2 : J ∣ Ideal.span {c} := by
    rw [← Ideal.dvd_iff_le] at this
    exact (mul_dvd_mul_iff_left hI).1 this
  exact (Ideal.span_singleton_le_iff_mem _).1 (Ideal.dvd_iff_le.1 h2)

variable {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (B : LinearMap.BilinForm F V)

theorem dual_anti {M L : Submodule (𝓞 F) V} (h : M ≤ L) :
    B.dualSubmodule L ≤ B.dualSubmodule M := fun _ hy x hx => hy x (h hx)

theorem dual_step (M : Submodule (𝓞 F) V) (x : V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup := by
  have e1 : M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup =
      (M.comap (LinearMap.toSpanSingleton (𝓞 F) V x)).toAddSubgroup.index := by
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left]
    have := AddSubgroup.index_comap M.toAddSubgroup
      (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom
    rw [show (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom.range =
      (Submodule.span (𝓞 F) {x}).toAddSubgroup from by
        ext z; simp [Submodule.mem_span_singleton]] at this
    exact this.symm
  have e2 : (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup =
      ((1 : Submodule (𝓞 F) F).toAddSubgroup.comap (B.flip x).toAddMonoidHom) ⊓
        (B.dualSubmodule M).toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, LinearMap.BilinForm.mem_dualSubmodule,
      AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    constructor
    · intro h
      exact ⟨h x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)),
        fun z hz => h z (Submodule.mem_sup_left hz)⟩
    · rintro ⟨h1, h2⟩ z hz
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_add, LinearMap.map_smul_of_tower]
      exact add_mem (h2 m hm) (Submodule.smul_mem _ c h1)
  rw [e1, e2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  refine inv_relIndex_dvd _ _ ?_
  rintro _ ⟨y, hy, rfl⟩ i hi
  have := hy (i • x) hi
  rwa [LinearMap.map_smul_of_tower] at this

theorem dual_relIndex_dvd (M : Submodule (𝓞 F) V) (s : Finset V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) (s : Set V))).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) (s : Set V)).toAddSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s _ ih =>
    have e : M ⊔ Submodule.span (𝓞 F) ((insert x s : Finset V) : Set V) =
        (M ⊔ Submodule.span (𝓞 F) (s : Set V)) ⊔ Submodule.span (𝓞 F) {x} := by
      rw [Finset.coe_insert, Submodule.span_insert, sup_assoc, sup_comm (Submodule.span _ {x})]
    rw [e]
    set N := M ⊔ Submodule.span (𝓞 F) (s : Set V) with hN
    have hMN : M ≤ N := le_sup_left
    rw [← AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup N.toAddSubgroup
      (N ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup hMN (le_sup_left (a := N)),
      ← AddSubgroup.relIndex_mul_relIndex _ (B.dualSubmodule N).toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup (dual_anti B (le_sup_left (a := N))) (dual_anti B hMN),
      mul_comm]
    exact mul_dvd_mul ih (dual_step B N x)

theorem dual_relIndex_dvd' {M L : Submodule (𝓞 F) V} (h : M ≤ L) (hL : L.FG) :
    (B.dualSubmodule L).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨s, hs⟩ := hL
  have := dual_relIndex_dvd B M s
  rwa [hs, sup_eq_right.2 h] at this

theorem span_eq_closure [Module ℚ V] [IsScalarTower ℚ F V] {n : ℕ} (b : Module.Basis (Fin n) F V) :
    (Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup =
      AddSubgroup.closure (Set.range ((integralBasis F).smulTower b)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine sum_mem fun j _ => ?_
    rw [← (RingOfIntegers.basis F).sum_repr (f j), Finset.sum_smul]
    refine sum_mem fun i _ => ?_
    rw [smul_assoc]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
      (Set.mem_range.2 ⟨(i, j), ?_⟩)) _
    rw [Module.Basis.smulTower_apply, integralBasis_apply, algebraMap_smul]
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [Module.Basis.smulTower_apply, integralBasis_apply, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem relIndex_span_eq_norm {n : ℕ} (b c : Module.Basis (Fin n) F V)
    (h : Submodule.span (𝓞 F) (Set.range b) ≤ Submodule.span (𝓞 F) (Set.range c)) :
    (((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 F) (Set.range c)).toAddSubgroup : ℕ) : ℚ) =
      |Algebra.norm ℚ (c.det b)| := by
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ F)
  haveI : IsScalarTower ℚ F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Free F V := Module.Free.of_basis b
  rw [AddSubgroup.relIndex_eq_abs_det _ _ h _ _ (span_eq_closure b) (span_eq_closure c)]
  set f : V →ₗ[F] V := (c.equiv b (Equiv.refl _)).toLinearMap with hf
  have h1 : (b : Fin n → V) = f ∘ c := by ext i; simp [hf]
  have h2 : (((integralBasis F).smulTower b : Module.Basis _ ℚ V) : _ → V) =
      (f.restrictScalars ℚ) ∘ ((integralBasis F).smulTower c) := by
    ext ⟨i, j⟩
    simp only [Function.comp_apply, Module.Basis.smulTower_apply, LinearMap.restrictScalars_apply,
      map_smul]
    rw [h1]; rfl
  rw [h2, Module.Basis.det_comp, Module.Basis.det_self, mul_one, LinearMap.det_restrictScalars]
  conv_rhs => rw [h1, Module.Basis.det_comp, Module.Basis.det_self, mul_one]

theorem mem_one_iff (z : F) : z ∈ (1 : Submodule (𝓞 F) F) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨c, rfl⟩; exact c.isIntegral_coe
  · intro h; exact ⟨⟨z, h⟩, rfl⟩

end GlobalTheory.DualIndex

open GlobalTheory.DualIndex in

theorem GlobalTheory.abs_norm_det_gram_eq_relIndex : ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (n : ℕ) (b : Module.Basis (Fin n) F V) (B : LinearMap.BilinForm F V) (L : AddSubgroup V), B.IsSymm → B.Nondegenerate → (∀ i, b i ∈ L) → (∀ (a : 𝓞 F) x, x ∈ L → a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (B x y)) → |((Algebra.norm ℚ (Matrix.of fun i j => B (b i) (b j)).det : ℚ) : ℝ)| = (L.relIndex (AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)}) : ℝ) * ((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex L : ℝ) ^ 2 := by
  intro F _ _ V _ _ _ _ n b B L hs hB hb hL hint
  classical
  let Λ : Submodule (𝓞 F) V :=
    { L.toAddSubmonoid with smul_mem' := fun a x hx => hL a x hx }
  have hΛ : Λ.toAddSubgroup = L := rfl
  set M := Submodule.span (𝓞 F) (Set.range b) with hM
  have hcl : AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)} =
      (B.dualSubmodule Λ).toAddSubgroup := by
    rw [← AddSubgroup.closure_eq (B.dualSubmodule Λ).toAddSubgroup]
    congr 1
    ext y
    change (∀ x ∈ L, IsIntegral ℤ (B x y)) ↔ ∀ x ∈ L, B y x ∈ (1 : Submodule (𝓞 F) F)
    refine forall₂_congr fun x _ => ?_
    rw [mem_one_iff, hs.eq x y]
  have hML : M ≤ Λ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hLL : Λ ≤ B.dualSubmodule Λ := fun x hx y hy => (mem_one_iff _).2 (hint x hx y hy)
  have hLM : B.dualSubmodule Λ ≤ B.dualSubmodule M := dual_anti B hML
  have hdual := B.dualSubmodule_span_of_basis (R := 𝓞 F) hB b
  have hdd := B.dualSubmodule_dualSubmodule_of_basis (R := 𝓞 F) hB hs b
  rw [← hM] at hdual hdd
  have hfg : (B.dualSubmodule M).FG := by
    rw [hdual]; exact Submodule.fg_span (Set.finite_range _)
  have hfgΛ : Λ.FG := Submodule.FG.of_le hfg (hLL.trans hLM)
  have d1 := dual_relIndex_dvd' B hML hfgΛ
  have d2 := dual_relIndex_dvd' B hLM hfg
  rw [hdd] at d2
  have hΛdd : Λ ≤ B.dualSubmodule (B.dualSubmodule Λ) := fun x hx y hy => by
    rw [hs.eq x y]; exact hy x hx
  have d3 := relIndex_dvd_of_le_right M.toAddSubgroup Λ.toAddSubgroup
    (B.dualSubmodule (B.dualSubmodule Λ)).toAddSubgroup (hML.trans hΛdd) hΛdd
  have hb' := Nat.dvd_antisymm d1 (d3.trans d2)
  have hle : M ≤ Submodule.span (𝓞 F) (Set.range (B.dualBasis hB b)) := by
    rw [← hdual]; exact hML.trans (hLL.trans hLM)
  have ha := relIndex_span_eq_norm b (B.dualBasis hB b) hle
  rw [← hM, ← hdual, ← AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup Λ.toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup hML (hLL.trans hLM),
    ← AddSubgroup.relIndex_mul_relIndex Λ.toAddSubgroup (B.dualSubmodule Λ).toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup hLL hLM, hb'] at ha
  have hdet : (B.dualBasis hB b).det b = (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.BilinForm.dualBasis_repr_apply]
  rw [hdet, hΛ] at ha
  rw [hcl, ← Rat.cast_abs, ← ha]
  push_cast
  ring

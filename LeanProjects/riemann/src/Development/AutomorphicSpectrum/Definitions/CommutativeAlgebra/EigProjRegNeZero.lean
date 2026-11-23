import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatTest

open Module NumberField TensorProduct

section Norms

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

theorem latNorm_span (hv : v.Integers O) {g : V} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  apply IsLeast.csInf_eq
  refine ⟨⟨c, rfl, g, Submodule.mem_span_singleton_self g, rfl⟩, ?_⟩
  rintro r ⟨a, rfl, y, hy, h⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [← IsScalarTower.algebraMap_smul C o g, smul_smul] at h
  have h2 := smul_left_injective C hg h
  rw [h2, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one o)

theorem mem_grLat {n : ℕ} (L : Submodule O V) (b : Basis (Fin n) C V) (i : Fin n) {x : V}
    (hx : x ∈ L) (hF : x ∈ b.flag i.succ) : b.repr x i ∈ grLat L b i :=
  ⟨x, ⟨hx, hF⟩, rfl⟩

theorem grLat_diag {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n) :
    grLat (Submodule.span O (Set.range fun j => c j • b j)) b i = Submodule.span O {c i} := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    change b.coord i x ∈ _
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨j, rfl⟩ := h
      by_cases hj : j = i
      · subst hj; simp
      · simp [Finsupp.single_apply, hj]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨c i • b i, ⟨Submodule.subset_span ⟨i, rfl⟩, ?_⟩, by simp⟩
    exact Submodule.smul_mem (b.flag i.succ) _ (b.self_mem_flag Fin.castSucc_lt_succ)

theorem grLog_diag (hv : v.Integers O) {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n)
    (hc : c i ≠ 0) :
    grLog v (Submodule.span O (Set.range fun j => c j • b j)) b i = -Real.log (v (c i)) := by
  have h := latNorm_span hv hc (c i)⁻¹
  rw [smul_eq_mul, inv_mul_cancel₀ hc] at h
  rw [grLog, grLat_diag, h, map_inv₀, NNReal.coe_inv, Real.log_inv]

theorem grLat_side (b : Basis (Fin 2) C V) :
    grLat (Submodule.span O {b 0 + b 1}) b 0 = ⊥ ∧
      grLat (Submodule.span O {b 0 + b 1}) b 1 = Submodule.span O {(1 : C)} := by
  constructor
  · rw [eq_bot_iff]
    rintro _ ⟨x, ⟨hx, hF⟩, rfl⟩
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have h1 := b.flag_le_ker_coord (k := (0 : Fin 2).succ) (l := 1) (by decide) hF
    rw [LinearMap.mem_ker, LinearMap.map_smul_of_tower] at h1
    have h2 : o • (1 : C) = 0 := by simpa using h1
    change b.coord 0 _ ∈ _
    rw [LinearMap.map_smul_of_tower]
    simpa using h2
  · apply le_antisymm
    · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hx
      change b.coord 1 _ ∈ _
      rw [LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ o (by simp)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨b 0 + b 1, ⟨Submodule.mem_span_singleton_self _, ?_⟩, by simp⟩
      exact Submodule.add_mem (b.flag (1 : Fin 2).succ) (b.self_mem_flag (by decide))
        (b.self_mem_flag (by decide))

theorem dualLat_span {c : C} (hc : c ≠ 0) :
    dualLat (LinearMap.mul C C) (Submodule.span O {c}) = Submodule.span O {c⁻¹} := by
  ext y
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h c (Submodule.mem_span_singleton_self c)
    refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
    rw [Algebra.smul_def, ho]; simp; field_simp
  · intro h x hx
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 h
    obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine ⟨o' * o, ?_⟩
    simp [Algebra.smul_def]; field_simp

end Norms

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem mem_eigSp {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
    ← integralBasis_apply, trace_dualInt]
  simp

theorem eigProj_mem (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    eigProj ρ σ x ∈ eigSp ρ σ := by
  classical
  haveI : CharZero K := (RingHom.charZero_iff σ.injective).1 inferInstance
  rw [mem_eigSp]
  intro a
  set b := RingOfIntegers.basis E
  have e1 : ∀ k, ρ a (ρ (b k) x) =
      ∑ j, σ ((Algebra.trace ℚ E (dualInt E j * (a : E) * integralBasis E k) : ℚ) : E) • ρ (b j) x := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul, ← b.sum_repr (a * b k), map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := repr_eq_trace (a * b k) j
    rw [map_zsmul, mul_assoc, integralBasis_apply]
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul (algebraMap (𝓞 E) E)] at this
    rw [RingOfIntegers.coe_eq_algebraMap, ← this]
    simp [Int.cast_smul_eq_zsmul, b]
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  change ∑ k, σ (dualInt E k) • ρ a (ρ (b k) x) = _
  simp only [e1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← map_mul, mul_comm (a : E), expand_dual (dualInt E j * (a : E)), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← expand_dual, ← map_mul, Rat.smul_def, mul_comm]

theorem sum_dualInt_mul : ∑ k, dualInt E k * integralBasis E k = 1 := by
  classical
  rw [← sub_eq_zero]
  apply (traceForm_nondegenerate ℚ E).1
  intro y
  rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, mul_assoc, mul_comm _ y]
  generalize y * integralBasis E k = z
  conv_lhs => rw [← (integralBasis E).sum_repr z]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, trace_dualInt]
  simp

theorem eigProj_of_mem {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} (hx : x ∈ eigSp ρ σ) :
    eigProj ρ σ x = x := by
  rw [mem_eigSp] at hx
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ, ← sum_dualInt_mul, map_sum]
    simp
  rw [this, one_smul]

theorem eigProj_of_ne {ρ : 𝓞 E →+* Module.End K V} {σ σ' : E →+* K} (h : σ ≠ σ') {x : V}
    (hx : x ∈ eigSp ρ σ') : eigProj ρ σ x = 0 := by
  have h1 := eigProj_mem ρ σ x
  have h2 : eigProj ρ σ x ∈ eigSp ρ σ' := by
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, mem_eigSp.1 hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  by_contra hne
  apply h
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  have := (mem_eigSp.1 h1 a).symm.trans (mem_eigSp.1 h2 a)
  exact smul_left_injective K hne this

theorem eigSub_le_eigQuot (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) :
    eigSub ρ σ X ≤ eigQuot ρ σ X ∧ eigQuot ρ σ X ≤ (eigSp ρ σ).restrictScalars A :=
  ⟨fun x hx => ⟨x, hx.1, eigProj_of_mem hx.2⟩, by rintro _ ⟨x, -, rfl⟩; exact eigProj_mem ρ σ x⟩

def regAct (K : Type) [Field K] (E : Type) [Field E] [NumberField E] :
    𝓞 E →+* Module.End K (K ⊗[ℤ] 𝓞 E) :=
  (Algebra.lmul K (K ⊗[ℤ] 𝓞 E)).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := K) (B := 𝓞 E)).toRingHom

theorem regAct_basis (k) :
    regAct K E (RingOfIntegers.basis E k) 1 =
      Algebra.TensorProduct.basis K (RingOfIntegers.basis E) k := by
  simp [regAct, Algebra.TensorProduct.basis_apply]

theorem eigProj_reg_ne_zero (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  intro h
  let φ : K ⊗[ℤ] 𝓞 E →ₐ[K] K := Algebra.TensorProduct.lift (AlgHom.id K K)
    (σ.comp (algebraMap (𝓞 E) E)).toIntAlgHom (fun _ _ => Commute.all _ _)
  have h1 := congrArg φ h
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, regAct_basis,
    Algebra.TensorProduct.basis_apply, map_zero] at h1
  have h2 : ∑ k, σ (dualInt E k * integralBasis E k) = 0 := by
    simpa [φ] using h1
  rw [← map_sum, sum_dualInt_mul, map_one] at h2
  exact one_ne_zero h2

theorem isFreeOn_reg :
    IsFreeOn (A := A) (regAct K E)
      (Submodule.span A (Set.range (Algebra.TensorProduct.basis K (RingOfIntegers.basis E))))
      (fun _ : Fin 1 => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [regAct_basis]
    exact (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent.comp
      (fun q : Fin 1 × _ => q.2) (fun p q h => Prod.ext (Subsingleton.elim _ _) h)
  · rw [Submodule.span_span_of_tower, Basis.span_eq]
  · simp only [regAct_basis]
    congr 1
    ext x
    simp

theorem diffAbs_bounds (v : Valuation K NNReal) (σ : E →+* K) :
    0 < diffAbs v σ ∧ diffAbs v σ ≤ 1 ∧
      ∀ x ∈ differentIdeal ℤ (𝓞 E), v (σ (x : E)) ≤ diffAbs v σ := by
  have hle : ∀ x : 𝓞 E, v (σ (x : E)) ≤ 1 := fun x => by
    have hi : IsIntegral ℤ (σ (x : E)) := x.isIntegral_coe.map σ.toIntAlgHom
    have hi' : IsIntegral v.integer (σ (x : E)) := hi.tower_top
    exact (Valuation.integer.integers v).mem_of_integral hi'
  have hb : BddAbove (Set.range fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E))) :=
    ⟨1, by rintro _ ⟨x, rfl⟩; exact hle x⟩
  have h3 : ∀ x ∈ differentIdeal ℤ (𝓞 E), v (σ (x : E)) ≤ diffAbs v σ :=
    fun x hx => le_ciSup hb ⟨x, hx⟩
  refine ⟨?_, ciSup_le fun x => hle x, h3⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  refine lt_of_lt_of_le ?_ (h3 x hx)
  rw [pos_iff_ne_zero, Valuation.ne_zero_iff, map_ne_zero]
  exact_mod_cast hx0

theorem diffAbs_of_span (v : Valuation K NNReal) (σ : E →+* K) {δ : 𝓞 E}
    (h : differentIdeal ℤ (𝓞 E) = Ideal.span {δ}) : diffAbs v σ = v (σ (δ : E)) := by
  refine le_antisymm (ciSup_le fun x => ?_)
    ((diffAbs_bounds v σ).2.2 δ (h ▸ Ideal.mem_span_singleton_self δ))
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (h.le x.2)
  have hi : IsIntegral ℤ (σ (y : E)) := y.isIntegral_coe.map σ.toIntAlgHom
  have hi' : IsIntegral v.integer (σ (y : E)) := hi.tower_top
  have h1 : v (σ (y : E)) ≤ 1 := (Valuation.integer.integers v).mem_of_integral hi'
  rw [← hy, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_mul]
  exact mul_le_of_le_one_left' h1

end Eigen

section Further

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

theorem grLat_shear (b : Basis (Fin 2) C V) (a : C) :
    grLat (Submodule.span O {b 0, a • b 0 + b 1}) b 0 = Submodule.span O {(1 : C)} := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hF⟩, rfl⟩
    obtain ⟨o, o', rfl⟩ := Submodule.mem_span_pair.1 hx
    have h1 := b.flag_le_ker_coord (k := (0 : Fin 2).succ) (l := 1) (by decide) hF
    rw [LinearMap.mem_ker, map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower] at h1
    have h2 : o' • (1 : C) = 0 := by simpa using h1
    change b.coord 0 _ ∈ _
    rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
    have h3 : o' • a = 0 := by rw [← one_mul a, ← smul_mul_assoc, h2, zero_mul]
    refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
    simp [h3]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨b 0, ⟨Submodule.subset_span (by simp), b.self_mem_flag (by decide)⟩, by simp⟩

theorem grLog_padic (p : ℕ) [Fact p.Prime] {n : ℕ} (i : Fin n) :
    grLog (Valued.v : Valuation ℂ_[p] NNReal)
      (Submodule.span 𝓞_ℂ_[p] (Set.range fun j => (p : ℂ_[p]) • Pi.basisFun ℂ_[p] (Fin n) j))
      (Pi.basisFun ℂ_[p] (Fin n)) i = Real.log p := by
  have hp : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [grLog_diag (PadicComplexInt.integers p) _ (fun _ => (p : ℂ_[p])) i hp,
    PadicComplex.valuation_p]
  simp

end Further

section FurtherEigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [Algebra A K] [IsScalarTower A K V] in

theorem isFreeOn_zero {ρ : 𝓞 E →+* Module.End K V} {X : Submodule A V} {t : Fin 0 → V}
    (h : IsFreeOn ρ X t) : Subsingleton V := by
  have h1 := h.2.1
  rw [h.2.2, Set.range_eq_empty, Submodule.span_empty] at h1
  refine subsingleton_of_forall_eq 0 fun y => ?_
  have : y ∈ (⊤ : Submodule K V) := trivial
  rw [← h1] at this
  simpa using this

theorem isFreeOn_stable {ρ : 𝓞 E →+* Module.End K V} {X : Submodule A V} {N : ℕ} {t : Fin N → V}
    (h : IsFreeOn ρ X t) (a : 𝓞 E) {x : V} (hx : x ∈ X) : ρ a x ∈ X := by
  rw [h.2.2] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    rw [← Module.End.mul_apply, ← map_mul,
      ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E q.2), map_sum,
      LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    exact Submodule.subset_span ⟨(q.1, k), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx

theorem eigSub_ne_eigQuot [CharZero K] {v : Valuation K NNReal} (hv : v.Integers A)
    {ρ : 𝓞 E →+* Module.End K V} {X : Submodule A V} {t : Fin 1 → V} (h : IsFreeOn ρ X t)
    (σ : E →+* K) (hd : diffAbs v σ < 1) : eigSub ρ σ X ≠ eigQuot ρ σ X := by
  intro he
  obtain ⟨hσ, d, hd0, hdv, hsp⟩ := exists_diff_generator K v A hv E σ
  obtain ⟨h1, h2, h3, -⟩ := SubDiffQuot.eigSub_eq_different_smul_eigQuot A K V E ρ X 1 t σ d
    hv.hom_inj hσ hsp h
  have hg : eigProj ρ σ (t 0) ≠ 0 := h3.ne_zero 0
  have h4 : eigQuot ρ σ X = Submodule.span A {eigProj ρ σ (t 0)} := by
    rw [h2, Set.range_unique]; rfl
  have h5 : (algebraMap A K d)⁻¹ • eigProj ρ σ (t 0) ∈ eigQuot ρ σ X := by
    rw [h1, he, ← IsScalarTower.algebraMap_smul K d, smul_smul, mul_inv_cancel₀ hd0, one_smul, h4]
    exact Submodule.mem_span_singleton_self _
  rw [h4] at h5
  have h6 := LatBasic.latNorm_le v (1 : K) h5
  rw [one_smul, latNorm_span hv hg, map_inv₀, map_one, hdv] at h6
  exact absurd ((inv_le_one₀ (LatBasic.diffAbs_pos v σ)).1 h6) (not_le.2 hd)

theorem diffAbs_gauss [IsCyclotomicExtension {4} ℚ E] (v : Valuation K NNReal) (σ : E →+* K) :
    diffAbs v σ = v 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ E
  have hadj := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  have hQ : Algebra.adjoin ℚ {algebraMap (𝓞 E) E hζ.toInteger} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have h := conductor_mul_differentIdeal ℤ ℚ E hζ.toInteger hQ
  have hm : minpoly ℤ hζ.toInteger = Polynomial.X ^ 2 + 1 := by
    rw [← minpoly.algebraMap_eq (RingOfIntegers.coe_injective (K := E)) hζ.toInteger]
    change minpoly ℤ (IsCyclotomicExtension.zeta 4 ℚ E) = _
    rw [← Polynomial.cyclotomic_eq_minpoly hζ (by norm_num)]
    have := Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two
    norm_num [Finset.sum_range_succ] at this
    rw [this]; ring
  rw [conductor_eq_top_of_adjoin_eq_top hadj, Ideal.top_mul, hm] at h
  rw [diffAbs_of_span v σ h]
  have h4 : v (σ (IsCyclotomicExtension.zeta 4 ℚ E)) = 1 := by
    have : v (σ (IsCyclotomicExtension.zeta 4 ℚ E)) ^ 4 = 1 := by
      rw [← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).1 this
  have h5 : ((Polynomial.aeval hζ.toInteger (Polynomial.derivative (Polynomial.X ^ 2 + 1 : Polynomial ℤ)) : 𝓞 E) : E)
      = 2 * IsCyclotomicExtension.zeta 4 ℚ E := by
    simp; norm_num; rw [map_ofNat, map_ofNat]; rfl
  rw [h5, map_mul, map_mul, h4, mul_one, map_ofNat]

theorem gauss_two [IsCyclotomicExtension {4} ℚ E] (σ : E →+* ℂ_[2]) :
    diffAbs (Valued.v : Valuation ℂ_[2] NNReal) σ = 1 / 2 ∧
      eigSub (A := 𝓞_ℂ_[2]) (LatBasic.regAct ℂ_[2] E) σ (Submodule.span _
          (Set.range (Algebra.TensorProduct.basis ℂ_[2] (RingOfIntegers.basis E)))) ≠
        eigQuot (LatBasic.regAct ℂ_[2] E) σ (Submodule.span _
          (Set.range (Algebra.TensorProduct.basis ℂ_[2] (RingOfIntegers.basis E)))) := by
  have h : diffAbs (Valued.v : Valuation ℂ_[2] NNReal) σ = 1 / 2 := by
    rw [diffAbs_gauss]
    exact_mod_cast PadicComplex.valuation_p 2
  exact ⟨h, eigSub_ne_eigQuot (PadicComplexInt.integers 2) LatBasic.isFreeOn_reg σ
    (by rw [h]; norm_num)⟩

theorem gauss_two_nonempty : Nonempty (CyclotomicField 4 ℚ →+* ℂ_[2]) :=
  ⟨(IsAlgClosed.lift : CyclotomicField 4 ℚ →ₐ[ℚ] ℂ_[2]).toRingHom⟩

theorem gauss_two_exists : ∃ σ : CyclotomicField 4 ℚ →+* ℂ_[2],
    diffAbs (Valued.v : Valuation ℂ_[2] NNReal) σ = 1 / 2 := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨σ⟩ := gauss_two_nonempty
  exact ⟨σ, (gauss_two σ).1⟩

end FurtherEigen

end GlobalTheory.CompanionTheory.Ar.HT.LatTest

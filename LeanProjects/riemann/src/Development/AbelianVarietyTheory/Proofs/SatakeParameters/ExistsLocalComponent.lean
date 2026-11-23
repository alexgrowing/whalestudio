import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

noncomputable section

namespace GlobalTheory.blockFieldPairProjections

open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct

section Completion

theorem exists_extension {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    (u : HeightOneSpectrum (𝓞 K)) (t : HeightOneSpectrum (𝓞 M)) (f : K →+* t.adicCompletion M)
    (h1 : ∀ r : 𝓞 K, Valued.v (f r) ≤ 1) (h2 : ∀ r : 𝓞 K, Valued.v (f r) < 1 ↔ r ∈ u.asIdeal) :
    ∃ φ : u.adicCompletion K →+* t.adicCompletion M, Continuous φ ∧
      ∀ x, φ (algebraMap K (u.adicCompletion K) x) = f x := by
  have key : ∀ x : K, ‖algebraMap K (u.adicCompletion K) x‖ < 1 → ‖f x‖ < 1 := by
    intro x hx
    rw [Valued.toNormedField.norm_lt_one_iff] at hx ⊢
    rw [adic_valued_algebraMap] at hx
    obtain ⟨a, d, had⟩ := u.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : (d : 𝓞 K) ∉ u.asIdeal := d.2
    have ha : a ∈ u.asIdeal := by
      rw [← u.valuation_lt_one_iff_mem (K := K)]
      have := congrArg (u.valuation K) had
      rw [map_mul, u.valuation_eq_one_iff_notMem.2 hd, mul_one] at this
      exact this ▸ hx
    have hd1 : Valued.v (f (d : 𝓞 K)) = 1 := le_antisymm (h1 _) (not_lt.1 fun h => hd ((h2 _).1 h))
    have := congrArg (fun y => Valued.v (f y)) had
    simp only [map_mul] at this
    have e : Valued.v (f x) = Valued.v (f a) := by
      rw [← mul_one (Valued.v (f x)), ← hd1]; exact this
    rw [e]; exact (h2 a).2 ha
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot u.ne_bot
  have hpK : (p : K) ≠ 0 := fun h => hp0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hfp : ‖f p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 ((h2 p).2 hp)
  letI : PseudoMetricSpace K := PseudoMetricSpace.induced (algebraMap K (u.adicCompletion K)) inferInstance
  have ue : IsUniformInducing (algebraMap K (u.adicCompletion K)) := ⟨rfl⟩
  have dr := HeightOneSpectrum.denseRange_algebraMap K u
  have hf : UniformContinuous f := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hfp
    have hj : 0 < ‖algebraMap K (u.adicCompletion K) ((p : K) ^ k)‖ := by
      rw [norm_pos_iff, map_ne_zero]; exact pow_ne_zero _ hpK
    refine ⟨_, hj, fun {a b} hab => ?_⟩
    have hab' : ‖algebraMap K (u.adicCompletion K) (a - b)‖ < ‖algebraMap K (u.adicCompletion K) ((p : K) ^ k)‖ := by
      rw [map_sub, ← dist_eq_norm]; exact hab
    have h3 := key ((a - b) / (p : K) ^ k) (by rw [map_div₀, norm_div, div_lt_one hj]; exact hab')
    have hq : 0 < ‖f ((p : K) ^ k)‖ := by
      rw [norm_pos_iff, map_ne_zero]; exact pow_ne_zero _ hpK
    rw [map_div₀, norm_div, div_lt_one hq, map_sub, map_pow, norm_pow] at h3
    rw [dist_eq_norm]
    exact h3.trans hk
  exact ⟨IsDenseInducing.extendRingHom ue dr hf, (uniformContinuous_uniformly_extend ue dr hf).continuous,
    fun x => uniformly_extend_of_ind ue dr hf x⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_equiv (s : SplitPlace L) :
    ∃ e : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous e ∧ Continuous e.symm ∧
      ∀ x : L, e (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  obtain ⟨φ, hφc, hφ⟩ := exists_extension s.w s.v s.i.toRingHom (fun r => s.split_le_one r)
    (fun r => (s.split_mem_ideal r).symm)
  obtain ⟨ψ, hψc, hψ⟩ := exists_extension s.v s.w
    ((algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L))
    (fun r => by
      rw [RingHom.comp_apply, adic_valued_algebraMap, ← split_coe_algebraMap]
      exact s.w.valuation_le_one _)
    (fun r => by
      rw [RingHom.comp_apply, adic_valued_algebraMap, ← split_coe_algebraMap, ← s.split_alg_mem]
      exact s.w.valuation_lt_one_iff_mem _)
  have h1 : ∀ y, φ (ψ y) = y := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).equalizer (hφc.comp hψc) continuous_id
      (by
        funext a
        simp only [Function.comp_apply, hψ, RingHom.comp_apply, hφ, id]
        exact s.i.commutes a)
    exact congrFun this
  have h2 : ∀ y, ψ (φ y) = y := fun y => φ.injective (h1 _)
  refine ⟨RingEquiv.ofRingHom ψ φ (RingHom.ext h2) (RingHom.ext h1), hψc, hφc, fun x => ?_⟩
  have := h2 (algebraMap L _ x)
  rw [hφ] at this
  exact this

end Completion

section Adeles

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem exists_imaginary (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : 𝓞 L, (δ : L) ≠ 0 ∧ IsCMField.complexConj L (δ : L) = -(δ : L) := by
  have : ∃ y : 𝓞 L, IsCMField.complexConj L (y : L) ≠ y := by
    by_contra h
    push Not at h
    apply IsCMField.complexConj_ne_one L
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h a) (h b)
  obtain ⟨y, hy⟩ := this
  refine ⟨y - IsCMField.ringOfIntegersComplexConj L y, ?_, ?_⟩
  · have : ((y - IsCMField.ringOfIntegersComplexConj L y : 𝓞 L) : L) = y - IsCMField.complexConj L y := by
      rw [← IsCMField.coe_ringOfIntegersComplexConj]; rfl
    rw [this]
    exact sub_ne_zero.2 hy.symm
  · have : ((y - IsCMField.ringOfIntegersComplexConj L y : 𝓞 L) : L) = y - IsCMField.complexConj L y := by
      rw [← IsCMField.coe_ringOfIntegersComplexConj]; rfl
    rw [this, map_sub, IsCMField.complexConj_apply_apply, neg_sub]

theorem exists_basis {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ) :
    ∃ b : Module.Basis (Fin 2) L⁺ L, b 0 = 1 ∧ b 1 = δ := by
  have hli : LinearIndependent L⁺ ![(1 : L), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    rw [Algebra.smul_def, Algebra.smul_def] at h
    have h' := congrArg (IsCMField.complexConj L) h
    rw [map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_one, hδ, map_zero] at h'
    have h1 : algebraMap L⁺ L a = 0 := by linear_combination (h + h') / 2
    have h2 : algebraMap L⁺ L t * δ = 0 := by linear_combination (h - h') / 2
    exact ⟨(map_eq_zero _).1 h1, (map_eq_zero _).1 ((mul_eq_zero.1 h2).resolve_right h0)⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, ?_, ?_⟩
  · rw [Algebra.IsQuadraticExtension.finrank_eq_two L⁺ L]; simp
  · simp
  · simp

theorem exists_coords {F V A : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
    (b : Module.Basis (Fin 2) F V) (z : V ⊗[F] A) : ∃ x y : A, z = b 0 ⊗ₜ x + b 1 ⊗ₜ y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul v a =>
    refine ⟨b.repr v 0 • a, b.repr v 1 • a, ?_⟩
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two, add_tmul, smul_tmul, smul_tmul]
  | add z z' h h' =>
    obtain ⟨x, y, rfl⟩ := h
    obtain ⟨x', y', rfl⟩ := h'
    exact ⟨x + x', y + y', by rw [tmul_add, tmul_add]; abel⟩

theorem coords_eq_zero {F V A : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup A] [Module F A]
    (b : Module.Basis (Fin 2) F V) {x y : A} (h : b 0 ⊗ₜ[F] x + b 1 ⊗ₜ[F] y = 0) : x = 0 ∧ y = 0 := by
  have h0 := congrArg ((TensorProduct.lid F A).toLinearMap ∘ₗ LinearMap.rTensor A (b.coord 0)) h
  have h1 := congrArg ((TensorProduct.lid F A).toLinearMap ∘ₗ LinearMap.rTensor A (b.coord 1)) h
  exact ⟨by simpa using h0, by simpa using h1⟩

theorem proj_tmul (s : SplitPlace L) (x : L) (a : AFplus L) : s.proj (x ⊗ₜ a) = s.i x * a s.v := rfl

theorem conj_tmul (x : L) (a : AFplus L) : conjAL L (x ⊗ₜ a) = IsCMField.complexConj L x ⊗ₜ a := rfl

theorem comp_tmul (u : HeightOneSpectrum (𝓞 L⁺)) (x : L) (a : AFplus L) : compAt L u (x ⊗ₜ a) = x ⊗ₜ a u := rfl

theorem adele_ext (s : SplitPlace L) {z z' : AL L} (h1 : s.proj z = s.proj z')
    (h2 : s.proj (conjAL L z) = s.proj (conjAL L z')) (h3 : ∀ u, u ≠ s.v → compAt L u z = compAt L u z') : z = z' := by
  obtain ⟨δ, h0, hδ⟩ := exists_imaginary L
  obtain ⟨b, hb0, hb1⟩ := exists_basis h0 hδ
  rw [← sub_eq_zero, ← map_sub] at h1
  rw [← sub_eq_zero, ← map_sub, ← map_sub] at h2
  have h3' : ∀ u, u ≠ s.v → compAt L u (z - z') = 0 := fun u hu => by rw [map_sub, h3 u hu, sub_self]
  rw [← sub_eq_zero]
  obtain ⟨x, y, hz⟩ := exists_coords b (z - z')
  rw [hz] at h1 h2 h3' ⊢
  have hd : s.i δ ≠ 0 := (map_ne_zero s.i).2 h0
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  rw [map_add, proj_tmul, proj_tmul, hb0, hb1, map_one] at h1
  rw [map_add, map_add, conj_tmul, conj_tmul, proj_tmul, proj_tmul, hb0, hb1, map_one, map_one, hδ, map_neg] at h2
  have key : ∀ u, x u = 0 ∧ y u = 0 := by
    intro u
    by_cases hu : u = s.v
    · subst hu
      have hy : s.i δ * y s.v = 0 := by linear_combination (h1 - h2) / 2
      exact ⟨by linear_combination (h1 + h2) / 2, (mul_eq_zero.1 hy).resolve_left hd⟩
    · have := h3' u hu
      rw [map_add, comp_tmul, comp_tmul] at this
      exact coords_eq_zero b this
  have hx : x = 0 := FiniteAdeleRing.ext _ fun u => (key u).1
  have hy : y = 0 := FiniteAdeleRing.ext _ fun u => (key u).2
  rw [hx, hy]; simp

open Classical in

def single (v : HeightOneSpectrum (𝓞 L⁺)) (a : v.adicCompletion L⁺) : AFplus L :=
  ⟨Pi.single (M := fun u : HeightOneSpectrum (𝓞 L⁺) => u.adicCompletion L⁺) v a, by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu
    rw [Pi.single_eq_of_ne hu]
    exact zero_mem _⟩

theorem single_self (v : HeightOneSpectrum (𝓞 L⁺)) (a : v.adicCompletion L⁺) : single v a v = a := by
  classical
  exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 L⁺) => u.adicCompletion L⁺) v a

theorem single_ne {v u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ v) (a : v.adicCompletion L⁺) : single v a u = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 L⁺) => u.adicCompletion L⁺) h a

theorem single_mul (v : HeightOneSpectrum (𝓞 L⁺)) (N : ℕ) (a : v.adicCompletion L⁺) :
    single v (N * a) = N • single v a := by
  refine FiniteAdeleRing.ext _ fun u => ?_
  have : (N • single v a) u = N • single v a u := map_nsmul (evalAt L u) N _
  rw [this]
  by_cases hu : u = v
  · subst hu; rw [single_self, single_self, nsmul_eq_mul]
  · rw [single_ne hu, single_ne hu, smul_zero]

def pair (s : SplitPlace L) (δ : L) (a b : s.v.adicCompletion L⁺) : AL L :=
  1 ⊗ₜ single s.v ((a + b) / 2) + δ ⊗ₜ single s.v ((a - b) / (2 * s.i δ))

theorem proj_pair (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (a b : s.v.adicCompletion L⁺) : s.proj (pair s δ a b) = a := by
  have hd : s.i δ ≠ 0 := (map_ne_zero s.i).2 h0
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  rw [pair, map_add, proj_tmul, proj_tmul, single_self, single_self, map_one]
  field_simp
  ring

theorem proj_conj_pair (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (a b : s.v.adicCompletion L⁺) : s.proj (conjAL L (pair s δ a b)) = b := by
  have hd : s.i δ ≠ 0 := (map_ne_zero s.i).2 h0
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  rw [pair, map_add, map_add, conj_tmul, conj_tmul, proj_tmul, proj_tmul, single_self, single_self, map_one, map_one,
    hδ, map_neg]
  field_simp
  ring

theorem comp_pair (s : SplitPlace L) (δ : L) (a b : s.v.adicCompletion L⁺) {u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ s.v) :
    compAt L u (pair s δ a b) = 0 := by
  rw [pair, map_add, comp_tmul, comp_tmul, single_ne h, single_ne h, tmul_zero, tmul_zero, add_zero]

theorem comp_conj_pair (s : SplitPlace L) (δ : L) (a b : s.v.adicCompletion L⁺) {u : HeightOneSpectrum (𝓞 L⁺)}
    (h : u ≠ s.v) : compAt L u (conjAL L (pair s δ a b)) = 0 := by
  rw [pair, map_add, map_add, conj_tmul, conj_tmul, comp_tmul, comp_tmul, single_ne h, single_ne h, tmul_zero, tmul_zero,
    add_zero]

theorem one_tmul_single_mem {v : HeightOneSpectrum (𝓞 L⁺)} {a : v.adicCompletion L⁺}
    (ha : a ∈ v.adicCompletionIntegers L⁺) : (1 : L) ⊗ₜ[L⁺] single v a ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨_, fun u => ?_, rfl⟩)
  by_cases hu : u = v
  · subst hu; rwa [single_self]
  · rw [single_ne hu]; exact zero_mem _

theorem pair_div (s : SplitPlace L) (δ : 𝓞 L) {N : ℕ} (hN : 0 < N) {a b : s.v.adicCompletion L⁺}
    (h1 : (a + b) / 2 / N ∈ s.v.adicCompletionIntegers L⁺)
    (h2 : (a - b) / (2 * s.i δ) / N ∈ s.v.adicCompletionIntegers L⁺) :
    ∃ y ∈ ALint L, pair s δ a b = (N : AL L) * y := by
  haveI : CharZero (s.v.adicCompletion L⁺) := charZero_of_injective_algebraMap (algebraMap L⁺ _).injective
  have hN' : (N : s.v.adicCompletion L⁺) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hδ : (δ : L) ⊗ₜ[L⁺] (1 : AFplus L) ∈ ALint L := Subring.subset_closure (Or.inl ⟨δ, rfl⟩)
  refine ⟨_, add_mem (one_tmul_single_mem h1) (mul_mem hδ (one_tmul_single_mem h2)), ?_⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← nsmul_eq_mul, smul_add, ← tmul_smul, ← tmul_smul,
    ← single_mul, ← single_mul, mul_div_cancel₀ _ hN', mul_div_cancel₀ _ hN', pair]

end Adeles

section Group

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

open Matrix

theorem matrix_ext (s : SplitPlace L) {X Y : Matrix (Fin n) (Fin n) (AL L)} (h1 : X.map s.proj = Y.map s.proj)
    (h2 : X.map (s.proj.comp (conjAL L)) = Y.map (s.proj.comp (conjAL L)))
    (h3 : ∀ u, u ≠ s.v → X.map (compAt L u) = Y.map (compAt L u)) : X = Y := by
  ext i j
  exact adele_ext s (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)
    fun u hu => congrFun (congrFun (h3 u hu) i) j

theorem map_conjT {R T : Type} [CommRing R] [CommRing T] (σ : R →+* R) (φ : R →+* T) (X : Matrix (Fin n) (Fin n) R) :
    (conjT σ X).map φ = (X.map (φ.comp σ))ᵀ := rfl

def liftMat (s : SplitPlace L) (δ : L) (g : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (AL L) :=
  1 + Matrix.of fun i j => pair s δ ((g.val - 1) i j) (((g⁻¹).val - 1) j i)

theorem map_one_add {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T) (X : Matrix (Fin n) (Fin n) R) :
    (1 + X).map φ = 1 + X.map φ := by
  rw [← RingHom.mapMatrix_apply, map_add, map_one, RingHom.mapMatrix_apply]

theorem liftMat_proj (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    (liftMat s δ g).map s.proj = g.val := by
  rw [liftMat, map_one_add]
  ext i j
  simp [proj_pair s h0]

theorem liftMat_proj_conj (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    (liftMat s δ g).map (s.proj.comp (conjAL L)) = (g⁻¹).valᵀ := by
  rw [liftMat, map_one_add]
  ext i j
  simp [proj_conj_pair s h0 hδ, Matrix.one_apply, eq_comm]

theorem liftMat_comp (s : SplitPlace L) (δ : L) (g : GL (Fin n) (s.v.adicCompletion L⁺))
    {u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ s.v) : (liftMat s δ g).map (compAt L u) = 1 := by
  rw [liftMat, map_one_add]
  ext i j
  simp [comp_pair s δ _ _ h]

theorem liftMat_comp_conj (s : SplitPlace L) (δ : L) (g : GL (Fin n) (s.v.adicCompletion L⁺))
    {u : HeightOneSpectrum (𝓞 L⁺)} (h : u ≠ s.v) : (liftMat s δ g).map ((compAt L u).comp (conjAL L)) = 1 := by
  rw [liftMat, map_one_add]
  ext i j
  simp [comp_conj_pair s δ _ _ h]

theorem comp_conj_conj {T : Type} [CommRing T] (φ : AL L →+* T) : (φ.comp (conjAL L)).comp (conjAL L) = φ :=
  RingHom.ext fun x => congrArg φ (conjAL_conjAL L x)

theorem liftMat_unitary (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : liftMat s δ g * conjT (conjAL L) (liftMat s δ g) = 1 := by
  refine matrix_ext s ?_ ?_ fun u hu => ?_
  · rw [Matrix.map_mul, map_conjT, liftMat_proj s h0, liftMat_proj_conj s h0 hδ, transpose_transpose, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, map_conjT, comp_conj_conj, liftMat_proj s h0, liftMat_proj_conj s h0 hδ, ← transpose_mul,
      Units.mul_inv, transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, map_conjT, liftMat_comp s δ g hu, liftMat_comp_conj s δ g hu, transpose_one, mul_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

def liftG (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : GA L n :=
  ⟨⟨liftMat s δ g, conjT (conjAL L) (liftMat s δ g), liftMat_unitary s h0 hδ g,
    mul_eq_one_comm.1 (liftMat_unitary s h0 hδ g)⟩, liftMat_unitary s h0 hδ g⟩

theorem loc_liftG (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : s.loc n (liftG s h0 hδ g) = g :=
  Units.ext (liftMat_proj s h0 g)

theorem triv_liftG (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) : TrivOutside {s.v} (liftG s h0 hδ g) :=
  fun _ hu => liftMat_comp s δ g hu

theorem triv_mul {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x y : GA L n} (hx : TrivOutside T x) (hy : TrivOutside T y) :
    TrivOutside T (x * y) := fun u hu => by
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx u hu, hy u hu, mul_one]

theorem eq_of_loc_eq (s : SplitPlace L) {x y : GA L n} (hx : TrivOutside {s.v} x) (hy : TrivOutside {s.v} y)
    (h : s.loc n x = s.loc n y) : x = y := by
  have h1 : x.1.val.map s.proj = y.1.val.map s.proj := congrArg Units.val h
  have inv : ∀ z : GA L n, z.1.val.map s.proj * (z.1.val.map (s.proj.comp (conjAL L)))ᵀ = 1 := fun z => by
    have hz : z.1.val * conjT (conjAL L) z.1.val = 1 := z.2
    rw [← map_conjT, ← Matrix.map_mul, hz, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Subtype.ext (Units.ext (matrix_ext s h1 ?_ fun u hu => (hx u hu).trans (hy u hu).symm))
  have a := inv x
  rw [h1] at a
  exact transpose_injective (Matrix.right_inv_eq_right_inv a (inv y))

def liftHom (s : SplitPlace L) {δ : L} (h0 : δ ≠ 0) (hδ : IsCMField.complexConj L δ = -δ) :
    GL (Fin n) (s.v.adicCompletion L⁺) →* GA L n :=
  MonoidHom.mk' (liftG s h0 hδ) fun a b =>
    eq_of_loc_eq s (triv_liftG s h0 hδ _) (triv_mul (triv_liftG s h0 hδ _) (triv_liftG s h0 hδ _))
      (by rw [map_mul, loc_liftG, loc_liftG, loc_liftG])

theorem eventually_cong (s : SplitPlace L) {δ : 𝓞 L} (h0 : (δ : L) ≠ 0) (hδ : IsCMField.complexConj L δ = -δ)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ g in nhds (1 : GL (Fin n) (s.v.adicCompletion L⁺)), Formalism.L2.NG.Cong L n N (liftG s h0 hδ g) := by
  have ho : IsOpen (s.v.adicCompletionIntegers L⁺ : Set (s.v.adicCompletion L⁺)) := Valued.isOpen_valuationSubring _
  have ca : ∀ i j, Continuous fun g : GL (Fin n) (s.v.adicCompletion L⁺) => (g.val - 1) i j := fun i j =>
    (Units.continuous_val.sub continuous_const).matrix_elem i j
  have cb : ∀ i j, Continuous fun g : GL (Fin n) (s.v.adicCompletion L⁺) => ((g⁻¹).val - 1) i j := fun i j =>
    (Units.continuous_coe_inv.sub continuous_const).matrix_elem i j
  have key : ∀ᶠ g in nhds (1 : GL (Fin n) (s.v.adicCompletion L⁺)), ∀ i j, ∃ y ∈ ALint L,
      pair s δ ((g.val - 1) i j) (((g⁻¹).val - 1) j i) = (N : AL L) * y := by
    simp only [Filter.eventually_all]
    intro i j
    have e1 := ((((ca i j).add (cb j i)).div_const 2).div_const (N : s.v.adicCompletion L⁺)).continuousAt.eventually_mem
      (x := 1) (ho.mem_nhds (by simp))
    have e2 := ((((ca i j).sub (cb j i)).div_const (2 * s.i δ)).div_const
      (N : s.v.adicCompletion L⁺)).continuousAt.eventually_mem (x := 1) (ho.mem_nhds (by simp))
    filter_upwards [e1, e2] with g h1 h2
    exact pair_div s δ hN h1 h2
  filter_upwards [key] with g hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨y, hy, e⟩ := hg i j
    show liftMat s δ g i j ∈ ALint L
    rw [liftMat, Matrix.add_apply, Matrix.of_apply, e]
    refine add_mem ?_ (mul_mem (natCast_mem _ _) hy)
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · obtain ⟨y, hy, e⟩ := hg i j
    refine ⟨y, hy, ?_⟩
    show liftMat s δ g i j - _ = _
    rw [liftMat, Matrix.add_apply, Matrix.of_apply, e, add_sub_cancel_left]

end Group

open Formalism.AUTREP Formalism.L2.NG in

theorem exists_local_component {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : FinTyp L n) (s : SplitPlace L)
    (W : Submodule ℂ (GAf L n → ℂ)) (hW : W ≤ π.S) (h0 : W ≠ ⊥)
    (hst : ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, rt L n x f ∈ W)
    (hirr : ∀ W' ≤ W, (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', rt L n x f ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), GlobalTheory.HeightCounting.IsLocS π.S s τ := by
  obtain ⟨e, he, he', hei⟩ := exists_equiv s
  obtain ⟨δ, hδ0, hδ⟩ := exists_imaginary L
  let b : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map e.symm.toRingHom
  have hb : Continuous b := by
    refine Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map he', ?_⟩
    simp only [← map_inv]
    exact Units.continuous_coe_inv.matrix_map he'
  have hbe : ∀ g, b (Matrix.GeneralLinearGroup.map e.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
  let ι : GL (Fin n) (s.w.adicCompletion L) →* GAf L n := (liftHom s hδ0 hδ).comp b
  have hι : ∀ g, TrivOutside {s.v} (ι g) := fun g => triv_liftG s hδ0 hδ _
  have hιx : ∀ x : GAf L n, TrivOutside {s.v} x → ι (Matrix.GeneralLinearGroup.map e.toRingHom (s.loc n x)) = x := by
    intro x hx
    refine eq_of_loc_eq s (hι _) hx ?_
    exact (loc_liftG s hδ0 hδ _).trans (hbe _)
  let ρ : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) W :=
    { toFun := fun g => (rt L n (ι g)).restrict (hst _ (hι g))
      map_one' := by
        ext f x
        show f.1 (x * ι 1) = f.1 x
        rw [map_one, mul_one]
      map_mul' := fun g h => by
        ext f x
        show f.1 (x * ι (g * h)) = f.1 (x * ι g * ι h)
        rw [map_mul, mul_assoc] }
  have hρ : ∀ g (f : W), (ρ g f : GAf L n → ℂ) = rt L n (ι g) f := fun _ _ => rfl
  have hsm : GlobalTheory.PRep.IsSmooth ρ := by
    intro f
    obtain ⟨N, hN, hf⟩ := π.smooth f (hW f.2)
    let K : Subgroup (GL (Fin n) (s.w.adicCompletion L)) :=
      { carrier := {g | ρ g f = f}
        one_mem' := by simp
        mul_mem' := fun {g h} hg hh => by
          have hg' : ρ g f = f := hg
          have hh' : ρ h f = f := hh
          show ρ (g * h) f = f
          rw [map_mul, Module.End.mul_apply, hh', hg']
        inv_mem' := fun {g} hg => by
          have hg' : ρ g f = f := hg
          show ρ g⁻¹ f = f
          conv_lhs => rw [← hg', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl }
    refine K.isOpen_of_mem_nhds (g := 1) ?_
    have h1 := eventually_cong (n := n) s hδ0 hδ hN
    rw [← map_one b] at h1
    filter_upwards [hb.continuousAt.eventually h1] with g hg
    exact Subtype.ext (hf _ hg)
  have hir : ρ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h => h0 <| (Submodule.eq_bot_iff _).2 fun f hf => by
      have : (⟨f, hf⟩ : W) ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [h]; trivial
      exact congrArg Subtype.val (show (⟨f, hf⟩ : W) = 0 from this)⟩
    refine ⟨fun R => ?_⟩
    rcases hirr (R.toSubmodule.map W.subtype) (Submodule.map_subtype_le _ _) (by
      rintro x hx _ ⟨f, hf, rfl⟩
      exact ⟨_, R.apply_mem_toSubmodule (Matrix.GeneralLinearGroup.map e.toRingHom (s.loc n x)) hf, by
        rw [Submodule.subtype_apply, hρ, hιx x hx]; rfl⟩) with h | h
    · left
      refine le_antisymm (fun f hf => ?_) bot_le
      have : (f : GAf L n → ℂ) ∈ R.toSubmodule.map W.subtype := ⟨f, hf, rfl⟩
      rw [h] at this
      exact Subtype.ext this
    · right
      refine le_antisymm le_top fun f _ => ?_
      have : (f : GAf L n → ℂ) ∈ R.toSubmodule.map W.subtype := by rw [h]; exact f.2
      obtain ⟨f', hf', e'⟩ := this
      obtain rfl : f' = f := Subtype.ext e'
      exact hf'
  refine ⟨⟨W, ρ, hsm, hir⟩, e, W.subtype, he, hei, W.injective_subtype, fun a => hW a.2, fun x hx a => ?_⟩
  exact (hρ _ a).trans (by rw [hιx x hx]; rfl)

end GlobalTheory.blockFieldPairProjections

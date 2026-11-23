import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.RadicalAlg

section General

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def mapsInto (U T : Submodule K V) : Submodule K (V →ₗ[K] V) where
  carrier := {X | ∀ y ∈ U, X y ∈ T}
  add_mem' := fun hX hY y hy => T.add_mem (hX y hy) (hY y hy)
  zero_mem' := fun _ _ => T.zero_mem
  smul_mem' := fun c _ hX y hy => T.smul_mem c (hX y hy)

omit [FiniteDimensional K V] in
theorem mem_mapsInto {U T : Submodule K V} {X : V →ₗ[K] V} :
    X ∈ mapsInto U T ↔ ∀ y ∈ U, X y ∈ T := Iff.rfl

theorem finrank_mapsInto (U T : Submodule K V) :
    (Module.finrank K (mapsInto U T) : ℤ) = (Module.finrank K V : ℤ) ^ 2 -
      Module.finrank K U * ((Module.finrank K V : ℤ) - Module.finrank K T) := by
  let Φ : (V →ₗ[K] V) →ₗ[K] (U →ₗ[K] (V ⧸ T)) :=
    (LinearMap.llcomp K U V (V ⧸ T) T.mkQ) ∘ₗ (LinearMap.lcomp K V U.subtype)
  have hk : LinearMap.ker Φ = mapsInto U T := by
    ext X
    simp only [LinearMap.mem_ker, mem_mapsInto, Φ, LinearMap.ext_iff]
    simp [Submodule.Quotient.mk_eq_zero]
  have hs : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro f
    obtain ⟨s, hs⟩ := T.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ T)
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (s ∘ₗ f)
    refine ⟨g, ?_⟩
    ext y
    have h1 := LinearMap.congr_fun hg y
    have h2 := LinearMap.congr_fun hs (f y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    simp only [Φ, LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.llcomp_apply]
    rw [h1, h2]
  have h := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hk, hs, finrank_top, Module.finrank_linearMap, Module.finrank_linearMap] at h
  have hq := Submodule.finrank_quotient_add_finrank T
  have hq' : (Module.finrank K (V ⧸ T) : ℤ) = Module.finrank K V - Module.finrank K T := by omega
  have h' : ((Module.finrank K U * Module.finrank K (V ⧸ T) + Module.finrank K (mapsInto U T) : ℕ) : ℤ)
    = (Module.finrank K V * Module.finrank K V : ℕ) := by rw [h]
  push_cast at h'
  rw [hq'] at h'
  linarith

theorem finrank_inf_mapsInto (S : Submodule K (V →ₗ[K] V)) (U U' : Submodule K V) (hU : U ≤ U')
    (h1 : mapsInto U ⊥ ≤ S) (h2 : S ≤ mapsInto U U) :
    (Module.finrank K ↥(S ⊓ mapsInto U' U) : ℤ) = Module.finrank K S -
      ((Module.finrank K U' : ℤ) - Module.finrank K U) *
        ((Module.finrank K V : ℤ) - Module.finrank K U) := by
  have hsup : S ⊔ mapsInto U' U = mapsInto U U := by
    refine le_antisymm (sup_le h2 fun X hX y hy => mem_mapsInto.mp hX y (hU hy)) ?_
    intro X hX
    obtain ⟨p, hp⟩ := LinearMap.exists_extend (LinearMap.id : U →ₗ[K] U)
    have e : X = (X - X ∘ₗ U.subtype ∘ₗ p) + X ∘ₗ U.subtype ∘ₗ p := by abel
    rw [e]
    refine Submodule.add_mem_sup (h1 fun y hy => ?_) fun y _ => hX _ (p y).2
    have := LinearMap.congr_fun hp ⟨y, hy⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (mapsInto U' U)
  rw [hsup] at h
  have h' : ((Module.finrank K (mapsInto U U) + Module.finrank K ↥(S ⊓ mapsInto U' U) : ℕ) : ℤ)
    = (Module.finrank K S + Module.finrank K (mapsInto U' U) : ℕ) := by rw [h]
  push_cast at h'
  rw [finrank_mapsInto, finrank_mapsInto] at h'
  linarith

theorem finrank_inf_flag (a : ℕ) : ∀ (F : Fin (a + 1) → Submodule K V) (S : Submodule K (V →ₗ[K] V)),
    Monotone F → mapsInto (F 0) ⊥ ≤ S → S ≤ mapsInto (F 0) (F 0) →
    (Module.finrank K ↥(S ⊓ ⨅ i : Fin a, mapsInto (F i.succ) (F i.castSucc)) : ℤ) = Module.finrank K S -
      ∑ i : Fin a, ((Module.finrank K (F i.succ) : ℤ) - Module.finrank K (F i.castSucc)) *
        ((Module.finrank K V : ℤ) - Module.finrank K (F i.castSucc)) := by
  induction a with
  | zero =>
    intro F S _ _ _
    rw [iInf_of_empty, inf_top_eq]
    simp
  | succ a ih =>
    intro F S hF h1 h2
    have h01 : F 0 ≤ F (Fin.succ 0) := hF (Fin.zero_le _)
    have hb : ∀ y ∈ (⊥ : Submodule K V), ∀ T : Submodule K V, y ∈ T := fun y hy T => bot_le (a := T) hy
    have := ih (fun i => F i.succ) (S ⊓ mapsInto (F (Fin.succ 0)) (F 0))
      (fun i k h => hF (Fin.succ_le_succ_iff.mpr h))
      (le_inf (fun X hX => h1 fun y hy => hX y (h01 hy)) fun X hX y hy => hb _ (hX y hy) _)
      (fun X hX y hy => h01 (hX.2 y hy))
    rw [finrank_inf_mapsInto S _ _ h01 h1 h2] at this
    have e : (S ⊓ ⨅ i : Fin (a + 1), mapsInto (F i.succ) (F i.castSucc)) =
        (S ⊓ mapsInto (F (Fin.succ 0)) (F 0)) ⊓
          ⨅ i : Fin a, mapsInto (F i.succ.succ) (F i.castSucc.succ) := by
      ext X
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Fin.forall_fin_succ, Fin.castSucc_zero,
        Fin.succ_castSucc, and_assoc]
    rw [e, this, Fin.sum_univ_succ, sub_sub]
    rfl

end General

theorem exists_orthonormal {n : ℕ} (P : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (hd : Module.finrank ℝ P = d) :
    ∃ E : Fin d → Matrix (Fin n) (Fin n) ℂ,
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧
      P = Submodule.span ℝ (Set.range E) := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := InnerProductSpace.complexToReal
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) :=
    { toFun := fun X => WithLp.toLp 2 fun p => X p.1 p.2
      invFun := fun v => Matrix.of fun i k => v (i, k)
      map_add' := fun X Y => by ext p; simp
      map_smul' := fun c X => by ext p; simp
      left_inv := fun X => by ext i k; simp
      right_inv := fun v => by ext p; simp }
  have hin : ∀ X Y, inner ℝ (e Y) (e X) = ((X * Yᴴ).trace).re := by
    intro X Y
    change (inner ℂ (e Y) (e X)).re = _
    congr 1
    simp [e, PiLp.inner_apply, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  let Q := P.map (e : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n))
  have hQ : Module.finrank ℝ Q = d := by rw [← hd]; exact LinearEquiv.finrank_map_eq e P
  let b := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
  refine ⟨fun i => e.symm (b i), fun i k => ?_, ?_⟩
  · rw [← hin, e.apply_symm_apply, e.apply_symm_apply]
    have := orthonormal_iff_ite.mp b.orthonormal k i
    rw [Submodule.coe_inner] at this
    rw [this]
    simp [eq_comm]
  · have h1 : Submodule.span ℝ (Set.range fun i => (b i : EuclideanSpace ℂ (Fin n × Fin n))) = Q := by
      have := congrArg (Submodule.map Q.subtype) b.toBasis.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
      simpa [Function.comp_def] using this
    have h2 : P = Q.map (e.symm : EuclideanSpace ℂ (Fin n × Fin n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) := by
      simp only [Q]
      rw [← Submodule.map_comp]
      simp
    have h3 := congrArg (Submodule.map
      (e.symm : EuclideanSpace ℂ (Fin n × Fin n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)) h1
    rw [Submodule.map_span, ← Set.range_comp, ← h2] at h3
    exact h3.symm

theorem finrank_fixed {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    [FiniteDimensional ℂ M]
    (σ : M →+ M) (hσ : ∀ x, σ (σ x) = x) (hc : ∀ (c : ℂ) x, σ (c • x) = star c • σ x)
    (S : Submodule ℂ M) (hS : ∀ x ∈ S, σ x ∈ S) (P : Submodule ℝ M)
    (hP : ∀ x, x ∈ P ↔ x ∈ S ∧ σ x = x) : Module.finrank ℝ P = Module.finrank ℂ S := by
  haveI : FiniteDimensional ℝ M := Module.Finite.trans ℂ M
  let m : M ≃ₗ[ℝ] M := (LinearEquiv.smulOfNeZero ℂ M Complex.I Complex.I_ne_zero).restrictScalars ℝ
  have hm : ∀ x, m x = Complex.I • x := fun x => rfl
  let P' := P.map (m : M →ₗ[ℝ] M)
  have hP' : Module.finrank ℝ P' = Module.finrank ℝ P := LinearEquiv.finrank_map_eq m P
  have hinf : P ⊓ P' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, y, hy, rfl⟩
    have h1 := ((hP _).mp hx).2
    have h2 := ((hP _).mp hy).2
    simp only [LinearEquiv.coe_coe, hm] at h1 ⊢
    rw [hc, h2] at h1
    have h3 : (2 : ℂ) • (Complex.I • y) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      simp
    simpa using h3
  have hsup : P ⊔ P' = S.restrictScalars ℝ := by
    apply le_antisymm
    · refine sup_le (fun x hx => ((hP _).mp hx).1) ?_
      rintro x ⟨y, hy, rfl⟩
      exact S.smul_mem _ ((hP _).mp hy).1
    · intro x hx
      have hx' : x ∈ S := hx
      have e : x = (1 / 2 : ℂ) • (x + σ x) + m ((-Complex.I / 2) • (x - σ x)) := by
        rw [hm, smul_smul]
        have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
          linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
        rw [this]
        module
      rw [e]
      refine Submodule.add_mem_sup ((hP _).mpr ⟨S.smul_mem _ (S.add_mem hx' (hS _ hx')), ?_⟩)
        ⟨_, (hP _).mpr ⟨S.smul_mem _ (S.sub_mem hx' (hS _ hx')), ?_⟩, rfl⟩
      · rw [hc, map_add, hσ, add_comm]; simp
      · rw [hc, map_sub, hσ]
        have : star (-Complex.I / 2) = Complex.I / 2 := by simp
        rw [this]
        module
  have h := Submodule.finrank_sup_add_finrank_inf_eq P P'
  rw [hsup, hinf, finrank_bot, hP'] at h
  have h2 : Module.finrank ℝ (S.restrictScalars ℝ) = 2 * Module.finrank ℂ S := by
    rw [← Complex.finrank_real_complex, Module.finrank_mul_finrank]
    rfl
  omega

section Form

open Formalism.REAL

variable {n : ℕ} (ε : Fin n → Bool)

def perp (U : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {y | ∀ x ∈ U, star x ⬝ᵥ (Jm ε *ᵥ y) = 0}
  add_mem' := fun hy hz x hx => by rw [mulVec_add, dotProduct_add, hy x hx, hz x hx, add_zero]
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c y hy x hx => by rw [mulVec_smul, dotProduct_smul, hy x hx, smul_zero]

theorem mem_perp {U : Submodule ℂ (Fin n → ℂ)} {y : Fin n → ℂ} :
    y ∈ perp ε U ↔ ∀ x ∈ U, star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := Iff.rfl

theorem finrank_perp (U : Submodule ℂ (Fin n → ℂ)) :
    Module.finrank ℂ U + Module.finrank ℂ (perp ε U) = n := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  have hJ : Matrix.toLin' (Jm ε) ∘ₗ Matrix.toLin' (Jm ε) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, Jm_mul_self, Matrix.toLin'_one]
  let eJ : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofLinear _ _ hJ hJ
  have hm : (perp ε U).map ((eJ.trans e : _ ≃ₗ[ℂ] _) : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
      (U.map (e : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))ᗮ := by
    ext z
    obtain ⟨y, rfl⟩ := (eJ.trans e).surjective z
    have hi : ∀ x, inner ℂ (e x) ((eJ.trans e) y) = star x ⬝ᵥ (Jm ε *ᵥ y) := fun x => by
      rw [dotProduct_comm]; rfl
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_orthogonal, mem_perp]
    constructor
    · rintro h _ ⟨x, hx, rfl⟩
      exact (hi x).trans (h x hx)
    · intro h x hx
      exact (hi x).symm.trans (h _ ⟨x, hx, rfl⟩)
  have h := Submodule.finrank_add_finrank_orthogonal
    (U.map (e : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))
  rw [← hm, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, finrank_euclideanSpace_fin] at h
  exact h

theorem form_symm (x y : Fin n → ℂ) : star y ⬝ᵥ (Jm ε *ᵥ x) = star (star x ⬝ᵥ (Jm ε *ᵥ y)) := by
  rw [star_dotProduct, star_mulVec, Jm_conjTranspose, dotProduct_mulVec]

theorem perp_perp (U : Submodule ℂ (Fin n → ℂ)) : perp ε (perp ε U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx y hy
    rw [form_symm, hy x hx, star_zero]
  · have h1 := finrank_perp ε U
    have h2 := finrank_perp ε (perp ε U)
    omega

theorem perp_anti {U T : Submodule ℂ (Fin n → ℂ)} (h : U ≤ T) : perp ε T ≤ perp ε U :=
  fun _ hy x hx => hy x (h hx)

def negAdj : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ where
  toFun X := -(Jm ε * Xᴴ * Jm ε)
  map_zero' := by simp
  map_add' X Y := by simp only [conjTranspose_add, mul_add, add_mul, neg_add]

theorem negAdj_apply (X : Matrix (Fin n) (Fin n) ℂ) : negAdj ε X = -(Jm ε * Xᴴ * Jm ε) := rfl

theorem negAdj_negAdj (X : Matrix (Fin n) (Fin n) ℂ) : negAdj ε (negAdj ε X) = X := by
  simp only [negAdj_apply, conjTranspose_neg, conjTranspose_mul, Jm_conjTranspose,
    conjTranspose_conjTranspose, mul_neg, neg_mul, neg_neg]
  rw [← mul_assoc, ← mul_assoc, Jm_mul_self, one_mul, mul_assoc, Jm_mul_self, mul_one]

theorem negAdj_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : negAdj ε (c • X) = star c • negAdj ε X := by
  simp only [negAdj_apply, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem negAdj_eq_iff (X : Matrix (Fin n) (Fin n) ℂ) : negAdj ε X = X ↔ inG ε X := by
  rw [negAdj_apply, inG]
  constructor
  · intro h
    nth_rewrite 2 [← h]
    rw [mul_neg, ← mul_assoc, ← mul_assoc, Jm_mul_self, one_mul, add_neg_cancel]
  · intro h
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, neg_neg, ← mul_assoc, Jm_mul_self, one_mul]

theorem negAdj_mapsInto {U T : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : Matrix.toLin' X ∈ mapsInto U T) :
    Matrix.toLin' (negAdj ε X) ∈ mapsInto (perp ε T) (perp ε U) := by
  intro y hy x hx
  have := hy _ (h x hx)
  rw [Matrix.toLin'_apply, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec] at this
  rw [Matrix.toLin'_apply, mulVec_mulVec, negAdj_apply, mul_neg, ← mul_assoc, ← mul_assoc, Jm_mul_self,
    one_mul, neg_mulVec, dotProduct_neg, this, neg_zero]

variable {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))

def lowering : Submodule ℂ ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :=
  (⊤ ⊓ ⨅ i : Fin a, mapsInto (W i.succ) (W i.castSucc)) ⊓ mapsInto (perp ε (W (Fin.last a))) (W (Fin.last a))

def fullLowering : Submodule ℂ ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :=
  lowering ε W ⊓ ⨅ i : Fin a, mapsInto (perp ε (W i.succ.rev)) (perp ε (W i.castSucc.rev))

theorem mem_lowering {X : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)} : X ∈ lowering ε W ↔
    (∀ i : Fin a, X ∈ mapsInto (W i.succ) (W i.castSucc)) ∧
      X ∈ mapsInto (perp ε (W (Fin.last a))) (W (Fin.last a)) := by
  simp [lowering]

theorem mem_fullLowering {X : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)} : X ∈ fullLowering ε W ↔
    X ∈ lowering ε W ∧ ∀ i : Fin a, X ∈ mapsInto (perp ε (W i.castSucc)) (perp ε (W i.succ)) := by
  simp only [fullLowering, Submodule.mem_inf, Submodule.mem_iInf, Fin.rev_succ, Fin.rev_castSucc]
  refine and_congr_right fun _ => ⟨fun h i => ?_, fun h i => h _⟩
  simpa using h i.rev

variable {ε W} {j : Fin a → ℕ}

theorem finrank_last (h : IsIsoFlag ε j W) : Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i := by
  obtain ⟨h0, -, h1, -⟩ := h
  have h2 : ∑ i : Fin (a + 1), Module.finrank ℂ (W i) = _ := Fin.sum_univ_succ _
  have h3 : ∑ i : Fin (a + 1), Module.finrank ℂ (W i) = _ := Fin.sum_univ_castSucc _
  rw [h0, finrank_bot] at h2
  simp only [h1, Finset.sum_add_distrib] at h2
  omega

theorem lowering_mapsInto (h : IsIsoFlag ε j W) {X : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)}
    (hX : ∀ i : Fin a, X ∈ mapsInto (W i.succ) (W i.castSucc)) (k : Fin (a + 1)) :
    X ∈ mapsInto (W k) (W k) := by
  intro y hy
  induction k using Fin.cases with
  | zero =>
    rw [h.1, Submodule.mem_bot] at hy
    rw [hy, map_zero]
    exact Submodule.zero_mem _
  | succ i => exact h.2.1 i.castSucc_lt_succ.le (hX i y hy)

theorem finrank_fullLowering (h : IsIsoFlag ε j W) : Module.finrank ℂ (fullLowering ε W) = dimN n j := by
  have hl := finrank_last h
  have hle : W (Fin.last a) ≤ perp ε (W (Fin.last a)) := fun y hy x hx => h.2.2.2 x hx y hy
  have hp := finrank_perp ε (W (Fin.last a))
  have hn : 2 * ∑ i, j i ≤ n := by
    have := Submodule.finrank_mono hle
    omega
  have hb : ∀ y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)), ∀ T : Submodule ℂ (Fin n → ℂ), y ∈ T :=
    fun y hy T => bot_le (a := T) hy
  have e1 := finrank_inf_flag a W ⊤ h.2.1 le_top (by
    intro X _ y hy
    rw [h.1, Submodule.mem_bot] at hy
    rw [hy, map_zero]
    exact Submodule.zero_mem _)
  have k1 : mapsInto (W (Fin.last a)) ⊥ ≤ ⊤ ⊓ ⨅ i : Fin a, mapsInto (W i.succ) (W i.castSucc) :=
    le_inf le_top (le_iInf fun i X hX y hy => hb _ (mem_mapsInto.mp hX y (h.2.1 (Fin.le_last _) hy)) _)
  have e2 := finrank_inf_mapsInto (⊤ ⊓ ⨅ i : Fin a, mapsInto (W i.succ) (W i.castSucc)) _ _ hle k1
    (fun X hX => lowering_mapsInto h ((Submodule.mem_iInf _).mp hX.2) _)
  have e3 := finrank_inf_flag a (fun k => perp ε (W k.rev)) (lowering ε W)
    (fun i k hik => perp_anti ε (h.2.1 (Fin.rev_le_rev.mpr hik)))
    (by
      rw [Fin.rev_zero]
      exact le_inf (fun X hX => k1 fun y hy => mem_mapsInto.mp hX y (hle hy))
        fun X hX y hy => hb _ (mem_mapsInto.mp hX y hy) _)
    (by
      rw [Fin.rev_zero]
      exact fun X hX y hy => hle (hX.2 y hy))
  have hp' : ∀ k, (Module.finrank ℂ (perp ε (W k)) : ℤ) = n - Module.finrank ℂ (W k) := fun k => by
    have := finrank_perp ε (W k)
    omega
  have hs : ∀ i : Fin a, (Module.finrank ℂ (W i.succ) : ℤ) = Module.finrank ℂ (W i.castSucc) + j i :=
    fun i => by rw [h.2.2.1 i]; push_cast; rfl
  have e3' : (Module.finrank ℂ (fullLowering ε W) : ℤ) = Module.finrank ℂ (lowering ε W) -
      ∑ i : Fin a, (j i : ℤ) * (Module.finrank ℂ (W i.castSucc) + j i) := by
    refine e3.trans ?_
    congr 1
    refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
    rw [Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc, hp', hp', hs, Module.finrank_fin_fun]
    ring
  have e2' : (Module.finrank ℂ (lowering ε W) : ℤ) = _ := e2
  rw [e1, finrank_top, Module.finrank_linearMap, hp', hl] at e2'
  simp only [hs, Module.finrank_fin_fun] at e2'
  have hsum : ∑ i : Fin a, ((Module.finrank ℂ (W i.castSucc) : ℤ) + j i - Module.finrank ℂ (W i.castSucc)) *
      ((n : ℤ) - Module.finrank ℂ (W i.castSucc)) +
      ∑ i : Fin a, (j i : ℤ) * (Module.finrank ℂ (W i.castSucc) + j i) =
      n * ∑ i, (j i : ℤ) + ∑ i, (j i : ℤ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq := GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a fun i => (j i : ℤ)
  have hd : (dimN n j : ℤ) = 4 * (∑ i, ∑ k, if i < k then (j i : ℤ) * j k else 0) +
      2 * (∑ i, (j i : ℤ)) * (n - 2 * ∑ i, (j i : ℤ)) + ∑ i, (j i : ℤ) ^ 2 := by
    simp only [dimN, Finset.sum_filter]
    push_cast [Nat.cast_sub hn]
    rfl
  push_cast at e2'
  have : (Module.finrank ℂ (fullLowering ε W) : ℤ) = dimN n j := by
    rw [e3', e2', hd]
    linear_combination -hsum + 2 * hsq
  exact_mod_cast this

end Form

theorem exists_algebra_flagN : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (dimN n j) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ flagN ε W = {g | uMat g - 1 ∈ A} := by
  intro n ε a j W h
  let t : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := Matrix.toLin'
  let A := ((lowering ε W).map t.symm.toLinearMap).restrictScalars ℝ
  have hA : ∀ X, X ∈ A ↔ Matrix.toLin' X ∈ lowering ε W := fun X => by
    simp only [A, Submodule.restrictScalars_mem]
    rw [Submodule.mem_map_equiv]; rfl
  let S := (fullLowering ε W).map t.symm.toLinearMap
  have hS : ∀ X, X ∈ S ↔ Matrix.toLin' X ∈ fullLowering ε W := fun X => by
    simp only [S]
    rw [Submodule.mem_map_equiv]; rfl
  have hSd : Module.finrank ℂ S = dimN n j :=
    (LinearEquiv.finrank_map_eq t.symm _).trans (finrank_fullLowering h)
  let P : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {X | X ∈ S ∧ negAdj ε X = X}
      add_mem' := fun hX hY => ⟨S.add_mem hX.1 hY.1, by rw [map_add, hX.2, hY.2]⟩
      zero_mem' := ⟨S.zero_mem, map_zero _⟩
      smul_mem' := fun c X hX => by
        have e : c • X = (c : ℂ) • X := rfl
        rw [Set.mem_setOf_eq, e]
        exact ⟨S.smul_mem _ hX.1, by rw [negAdj_smul, hX.2]; simp⟩ }
  have hst : ∀ X ∈ S, negAdj ε X ∈ S := by
    intro X hX
    rw [hS, mem_fullLowering, mem_lowering] at hX ⊢
    refine ⟨⟨fun i => ?_, ?_⟩, fun i => negAdj_mapsInto ε (hX.1.1 i)⟩
    · simpa only [perp_perp] using negAdj_mapsInto ε (hX.2 i)
    · simpa only [perp_perp] using negAdj_mapsInto ε hX.1.2
  have hPd : Module.finrank ℝ P = dimN n j :=
    (finrank_fixed (negAdj ε) (negAdj_negAdj ε) (negAdj_smul ε) S hst P fun _ => Iff.rfl).trans hSd
  obtain ⟨E, hE, hPE⟩ := exists_orthonormal P _ hPd
  refine ⟨A, E, ?_, hE, fun X => ?_, ?_⟩
  · intro X hX Y hY
    rw [hA, mem_lowering] at hX hY ⊢
    rw [Matrix.toLin'_mul]
    exact ⟨fun i y hy => lowering_mapsInto h hX.1 _ _ (hY.1 i y hy),
      fun y hy => lowering_mapsInto h hX.1 _ _ (hY.2 y hy)⟩
  · rw [← hPE, ← negAdj_eq_iff]
    change _ ↔ X ∈ S ∧ negAdj ε X = X
    refine and_congr_left fun hX => ?_
    rw [hA, hS, mem_fullLowering]
    refine ⟨fun h1 => ⟨h1, fun i => ?_⟩, fun h1 => h1.1⟩
    rw [← hX]
    exact negAdj_mapsInto ε (((mem_lowering ε W).mp h1).1 i)
  · ext g
    rw [Set.mem_setOf_eq, hA, mem_lowering]
    simp only [flagN, Set.mem_setOf_eq, mem_mapsInto, mem_perp, Matrix.toLin'_apply, sub_mulVec, one_mulVec]

end GlobalTheory.RadicalAlg

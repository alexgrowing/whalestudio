import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open scoped ComplexOrder
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.LeviAlgebra

variable {n : ℕ}

theorem trace_mul_mul (a b : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ a ∘ₗ LinearMap.mulRight ℂ b) = a.trace * b.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.stdBasis_eq_single]
  have : ∀ M : Matrix (Fin n) (Fin n) ℂ, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr M (i, k) = M i k := by
    intro M
    simp [Matrix.stdBasis]
  rw [this]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

def commutant {ι : Type} (e : ι → Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ k, X * e k = e k * X}
  add_mem' := by
    intro X Y hX hY k
    rw [add_mul, mul_add, hX k, hY k]
  zero_mem' := by intro k; simp
  smul_mem' := by
    intro c X hX k
    rw [Matrix.smul_mul, Matrix.mul_smul, hX k]

theorem finrank_commutant {ι : Type} [Fintype ι] (e : ι → Matrix (Fin n) (Fin n) ℂ)
    (he : CompleteOrthogonalIdempotents e) :
    (Module.finrank ℂ (commutant e) : ℂ) = ∑ k, (e k).trace ^ 2 := by
  classical
  have hp : LinearMap.IsProj (commutant e)
      (∑ k, LinearMap.mulLeft ℂ (e k) ∘ₗ LinearMap.mulRight ℂ (e k)) := by
    constructor
    · intro X k
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : l = k
      · subst h
        rw [mul_assoc, mul_assoc, (he.idem l).eq, ← mul_assoc (e l) (e l), (he.idem l).eq]
      · rw [mul_assoc, mul_assoc, he.ortho h, ← mul_assoc (e k) (e l), he.ortho (Ne.symm h)]
        simp
    · intro X hX
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply]
      have : ∀ k, e k * (X * e k) = e k * X := fun k => by
        rw [hX k, ← mul_assoc, (he.idem k).eq]
      simp only [this]
      rw [← Finset.sum_mul, he.complete, one_mul]
  rw [← hp.trace, map_sum]
  simp only [trace_mul_mul, sq]

theorem trace_of_proj (P : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ y, P *ᵥ y ∈ W) (h2 : ∀ y ∈ W, P *ᵥ y = y) : P.trace = Module.finrank ℂ W := by
  have hp : LinearMap.IsProj W (Matrix.toLin' P) := ⟨fun y => h1 y, fun y hy => h2 y hy⟩
  rw [← hp.trace, Matrix.trace_toLin'_eq]

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ (∀ y, P *ᵥ y ∈ W) ∧ ∀ y ∈ W, P *ᵥ y = y := by
  let W' : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := W.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := W'.starProjection.toLinearMap
  have hT : ∀ y : Fin n → ℂ, (Matrix.toEuclideanLin.symm T) *ᵥ y = (T (WithLp.toLp 2 y)).ofLp := by
    intro y
    conv_rhs => rw [← Matrix.toEuclideanLin.apply_symm_apply T]
    rfl
  refine ⟨Matrix.toEuclideanLin.symm T, ?_, fun y => ?_, fun y hy => ?_⟩
  · apply Matrix.isSymmetric_toEuclideanLin_iff.1
    rw [LinearEquiv.apply_symm_apply]
    exact W'.starProjection_isSymmetric
  · rw [hT]
    exact W'.starProjection_apply_mem (WithLp.toLp 2 y)
  · rw [hT]
    have : T (WithLp.toLp 2 y) = WithLp.toLp 2 y := Submodule.starProjection_eq_self_iff.2 hy
    rw [this]

theorem exists_orthonormal (G : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (hd : Module.finrank ℝ G = d) :
    ∃ E : Fin d → Matrix (Fin n) (Fin n) ℂ,
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ Submodule.span ℝ (Set.range E) = G := by
  subst hd
  let c : InnerProductSpace.Core ℝ G :=
    { inner := fun X Y => (((X : Matrix (Fin n) (Fin n) ℂ) * (Y : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re
      conj_inner_symm := by
        intro X Y
        have : (X : Matrix (Fin n) (Fin n) ℂ) * (Y : Matrix (Fin n) (Fin n) ℂ)ᴴ =
          ((Y : Matrix (Fin n) (Fin n) ℂ) * (X : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᴴ := by simp
        simp only [conj_trivial]
        rw [this, Matrix.trace_conjTranspose]
        simp
      re_inner_nonneg := by
        intro X
        have := (Matrix.posSemidef_self_mul_conjTranspose (X : Matrix (Fin n) (Fin n) ℂ)).trace_nonneg
        simpa using (Complex.le_def.1 this).1
      add_left := by
        intro X Y Z
        simp [add_mul]
      smul_left := by
        intro X Y r
        simp
      definite := by
        intro X hX
        have h := (Matrix.posSemidef_self_mul_conjTranspose (X : Matrix (Fin n) (Fin n) ℂ)).trace_nonneg
        have h2 : ((X : Matrix (Fin n) (Fin n) ℂ) * (X : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace = 0 :=
          Complex.ext hX (Complex.le_def.1 h).2.symm
        exact Subtype.ext (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 h2) }
  letI : NormedAddCommGroup G := c.toNormedAddCommGroup
  letI : InnerProductSpace ℝ G := InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℝ G
  refine ⟨fun i => b i, fun i k => ?_, ?_⟩
  · exact orthonormal_iff_ite.1 b.orthonormal i k
  · have := b.toBasis.span_eq
    have h2 := congrArg (Submodule.map G.subtype) this
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
    exact h2

theorem finrank_real_form (ε : Fin n → Bool) (C : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hC : ∀ X ∈ C, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ C) (G : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hG : ∀ X, X ∈ G ↔ X ∈ C ∧ Formalism.REAL.inG ε X) : Module.finrank ℝ G = Module.finrank ℂ C := by
  set J := Formalism.REAL.Jm ε with hJ
  have hJJ : J * J = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : Jᴴ = J := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by rw [← mul_assoc, hJJ, one_mul]
  let φ : (G × G) →ₗ[ℝ] C :=
    { toFun := fun p => ⟨(p.1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (p.2 : Matrix (Fin n) (Fin n) ℂ),
        C.add_mem ((hG _).1 p.1.2).1 (C.smul_mem _ ((hG _).1 p.2.2).1)⟩
      map_add' := by
        intro p q
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro r p
        apply Subtype.ext
        simp [smul_comm r Complex.I] }
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨X, Y⟩ h
      have h0 : (X : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (Y : Matrix (Fin n) (Fin n) ℂ) = 0 :=
        congrArg Subtype.val h
      have hX : (X : Matrix (Fin n) (Fin n) ℂ)ᴴ * J + J * X = 0 := ((hG _).1 X.2).2
      have hY : (Y : Matrix (Fin n) (Fin n) ℂ)ᴴ * J + J * Y = 0 := ((hG _).1 Y.2).2
      have h1 : (X : Matrix (Fin n) (Fin n) ℂ) = -(Complex.I • (Y : Matrix (Fin n) (Fin n) ℂ)) :=
        eq_neg_of_add_eq_zero_left h0
      have hY' : (Y : Matrix (Fin n) (Fin n) ℂ)ᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
      have h2 : (-(2 * Complex.I)) • (J * (Y : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
        rw [← hX, h1]
        simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.neg_mul, Matrix.smul_mul,
          Matrix.mul_neg, Matrix.mul_smul, hY', Complex.star_def, Complex.conj_I]
        module
      have h3 : J * (Y : Matrix (Fin n) (Fin n) ℂ) = 0 := by
        simpa using h2
      have h4 : (Y : Matrix (Fin n) (Fin n) ℂ) = 0 := by rw [← hJJ' Y, h3, mul_zero]
      have h5 : (X : Matrix (Fin n) (Fin n) ℂ) = 0 := by rw [h1, h4]; simp
      exact Prod.ext (Subtype.ext h5) (Subtype.ext h4)
    · rintro ⟨Z, hZ⟩
      refine ⟨(⟨(1 / 2 : ℂ) • (Z - J * Zᴴ * J), (hG _).2 ⟨C.smul_mem _ (C.sub_mem hZ (hC Z hZ)), ?_⟩⟩,
        ⟨(-Complex.I / 2) • (Z + J * Zᴴ * J), (hG _).2 ⟨C.smul_mem _ (C.add_mem hZ (hC Z hZ)), ?_⟩⟩), ?_⟩
      · unfold Formalism.REAL.inG
        rw [← hJ]
        simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH,
          Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub,
          mul_assoc, hJJ, hJJ', mul_one]
        simp
        module
      · unfold Formalism.REAL.inG
        rw [← hJ]
        simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
          Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
          mul_assoc, hJJ, hJJ', mul_one]
        simp
        module
      · apply Subtype.ext
        change (1 / 2 : ℂ) • (Z - J * Zᴴ * J) + Complex.I • ((-Complex.I / 2) • (Z + J * Zᴴ * J)) = Z
        rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
          rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
        module
  have h1 := (LinearEquiv.ofBijective φ hφ).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex] at h1
  omega

theorem keeps_iff_comm (W : Submodule ℂ (Fin n → ℂ)) (P : Matrix (Fin n) (Fin n) ℂ) (h0 : Pᴴ = P)
    (h1 : ∀ y, P *ᵥ y ∈ W) (h2 : ∀ y ∈ W, P *ᵥ y = y) (X : Matrix (Fin n) (Fin n) ℂ) :
    (∀ y ∈ W, X *ᵥ y ∈ W ∧ Xᴴ *ᵥ y ∈ W) ↔ X * P = P * X := by
  constructor
  · intro h
    have a1 : P * X * P = X * P := by
      apply Matrix.ext_of_mulVec_single
      intro i
      simp only [← Matrix.mulVec_mulVec]
      exact h2 _ (h _ (h1 _)).1
    have a2 : P * Xᴴ * P = Xᴴ * P := by
      apply Matrix.ext_of_mulVec_single
      intro i
      simp only [← Matrix.mulVec_mulVec]
      exact h2 _ (h _ (h1 _)).2
    have a3 := congrArg Matrix.conjTranspose a2
    simp only [Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_conjTranspose, ← mul_assoc] at a3
    rw [← a1, a3]
  · intro h y hy
    have a3 := congrArg Matrix.conjTranspose h
    simp only [Matrix.conjTranspose_mul, h0] at a3
    constructor
    · rw [← h2 y hy, Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
      exact h1 _
    · rw [← h2 y hy, Matrix.mulVec_mulVec, ← a3, ← Matrix.mulVec_mulVec]
      exact h1 _

theorem finrank_skew_commutant (ε : Fin n → Bool) {a : ℕ} (j : Fin a → ℕ)
    (u : Fin a → Matrix (Fin n) (Fin n) ℂ) (hu : OrthogonalIdempotents u) (hH : ∀ i, (u i)ᴴ = u i)
    (hiso : ∀ i k, u i * Formalism.REAL.Jm ε * u k = 0) (htr : ∀ i, (u i).trace = j i)
    (G : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hG : ∀ X, X ∈ G ↔ (∀ i, X * u i = u i * X) ∧ Formalism.REAL.inG ε X) :
    Module.finrank ℝ G = (n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2 := by
  set J := Formalism.REAL.Jm ε with hJ
  have hJJ : J * J = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : Jᴴ = J := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by rw [← mul_assoc, hJJ, one_mul]
  have hiso' : ∀ i k (X : Matrix (Fin n) (Fin n) ℂ), u i * (J * (u k * X)) = 0 := fun i k X => by
    rw [← mul_assoc, ← mul_assoc, hiso, zero_mul]
  let e : Fin a ⊕ Fin a → Matrix (Fin n) (Fin n) ℂ := Sum.elim u fun i => J * u i * J
  have he : OrthogonalIdempotents e := by
    constructor
    · rintro (i | i)
      · exact hu.idem i
      · change J * u i * J * (J * u i * J) = J * u i * J
        simp only [mul_assoc, hJJ']
        rw [← mul_assoc (u i) (u i), (hu.idem i).eq]
    · rintro (i | i) (k | k) hik
      · exact hu.ortho fun h => hik (by rw [h])
      · change u i * (J * u k * J) = 0
        simp only [mul_assoc, hiso']
      · change J * u i * J * u k = 0
        rw [mul_assoc J, mul_assoc J, hiso, mul_zero]
      · change J * u i * J * (J * u k * J) = 0
        simp only [mul_assoc, hJJ']
        rw [← mul_assoc (u i) (u k), hu.ortho fun h => hik (by rw [h])]
        simp
  have hc := CompleteOrthogonalIdempotents.option he
  have hmem : ∀ X, X ∈ commutant (fun x : Option (Fin a ⊕ Fin a) => x.elim (1 - ∑ i, e i) e) ↔
      (∀ i, X * u i = u i * X) ∧ ∀ i, X * (J * u i * J) = J * u i * J * X := by
    intro X
    constructor
    · intro h
      exact ⟨fun i => h (some (Sum.inl i)), fun i => h (some (Sum.inr i))⟩
    · intro h
      have h' : ∀ k, X * e k = e k * X := by
        rintro (i | i)
        exacts [h.1 i, h.2 i]
      rintro (_ | k)
      · change X * (1 - ∑ i, e i) = (1 - ∑ i, e i) * X
        simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, h', mul_one, one_mul]
      · exact h' k
  have hadj : ∀ (X p : Matrix (Fin n) (Fin n) ℂ), pᴴ = p → X * p = p * X →
      J * Xᴴ * J * (J * p * J) = J * p * J * (J * Xᴴ * J) := by
    intro X p hp h
    have a3 := congrArg Matrix.conjTranspose h
    simp only [Matrix.conjTranspose_mul, hp] at a3
    simp only [mul_assoc, hJJ']
    rw [← mul_assoc Xᴴ, ← a3, mul_assoc]
  have h1 := finrank_real_form ε (commutant (fun x : Option (Fin a ⊕ Fin a) => x.elim (1 - ∑ i, e i) e))
    (by
      intro X hX
      rw [hmem] at hX ⊢
      refine ⟨fun i => ?_, fun i => hadj X _ (hH i) (hX.1 i)⟩
      have := hadj X (J * u i * J) (by simp only [Matrix.conjTranspose_mul, hJH, hH, mul_assoc]) (hX.2 i)
      rwa [show J * (J * u i * J) * J = u i by simp only [mul_assoc, hJJ', hJJ, mul_one]] at this) G
    (by
      intro X
      rw [hG, hmem]
      refine ⟨fun h => ⟨⟨h.1, fun i => ?_⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      have hX : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left h.2
      have := hadj X _ (hH i) (h.1 i)
      rw [show J * Xᴴ * J = -X by rw [mul_assoc, hX, mul_neg, hJJ']] at this
      simpa using this)
  have h2 := finrank_commutant _ hc
  have htr' : ∀ i, (J * u i * J).trace = j i := fun i => by
    rw [Matrix.trace_mul_cycle, hJJ, one_mul, htr]
  have h3 : (1 - ∑ i, e i).trace = (n : ℂ) - 2 * ∑ i, (j i : ℂ) := by
    rw [Matrix.trace_sub, Matrix.trace_sum, Fintype.sum_sum_type]
    simp only [e, Sum.elim_inl, Sum.elim_inr, htr, htr', Matrix.trace_one, Fintype.card_fin]
    ring
  have h4 := trace_of_proj (1 - ∑ i, e i) (LinearMap.range (Matrix.toLin' (1 - ∑ i, e i)))
    (fun y => ⟨y, rfl⟩) (by
      rintro _ ⟨y, rfl⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      congr 1
      exact (hc.idem none).eq)
  generalize Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1 - ∑ i, e i))) = r at h4
  have h5 : n = r + 2 * ∑ i, j i := by
    have : (n : ℂ) = r + 2 * ∑ i, (j i : ℂ) := by rw [← h4, h3]; ring
    exact_mod_cast this
  have h6 : n - 2 * ∑ i, j i = r := by omega
  rw [h1, h6]
  generalize Module.finrank ℂ (commutant (fun x : Option (Fin a ⊕ Fin a) => x.elim (1 - ∑ i, e i) e)) = d at h2 ⊢
  rw [Fintype.sum_option] at h2
  simp only [Option.elim_none, Option.elim_some, h4] at h2
  rw [Fintype.sum_sum_type] at h2
  simp only [e, Sum.elim_inl, Sum.elim_inr, htr, htr'] at h2
  apply Nat.cast_injective (R := ℂ)
  refine h2.trans ?_
  push_cast
  ring

theorem exists_levi_algebra : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ flagM ε W = {g | uMat g - 1 ∈ A} := by
  intro n ε a j W ⟨h0, hmono, hrk, hiso⟩
  choose P hH h1 h2 using fun i => exists_proj (W i)
  have hPP : ∀ i k, i ≤ k → P k * P i = P i := by
    intro i k hik
    apply Matrix.ext_of_mulVec_single
    intro l
    simp only [← Matrix.mulVec_mulVec]
    exact h2 _ _ (hmono hik (h1 _ _))
  have hPP' : ∀ i k, i ≤ k → P i * P k = P i := by
    intro i k hik
    have := congrArg Matrix.conjTranspose (hPP i k hik)
    simpa only [Matrix.conjTranspose_mul, hH] using this
  have hP0 : P 0 = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro l
    have := h1 0 (Pi.single l 1)
    rw [h0, Submodule.mem_bot] at this
    rw [this, Matrix.zero_mulVec]
  have hPJ : ∀ i k, P i * Formalism.REAL.Jm ε * P k = 0 := by
    intro i k
    ext r s
    have := hiso _ (hmono (Fin.le_last i) (h1 i (Pi.single r 1))) _ (hmono (Fin.le_last k) (h1 k (Pi.single s 1)))
    rw [Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [Pi.star_single] using this
  let u : Fin a → Matrix (Fin n) (Fin n) ℂ := fun i => P i.succ - P i.castSucc
  have hu : OrthogonalIdempotents u := by
    constructor
    · intro i
      change (P i.succ - P i.castSucc) * (P i.succ - P i.castSucc) = P i.succ - P i.castSucc
      have hle : i.castSucc ≤ i.succ := i.castSucc_lt_succ.le
      rw [mul_sub, sub_mul, sub_mul, hPP _ _ le_rfl, hPP _ _ le_rfl, hPP _ _ hle, hPP' _ _ hle]
      abel
    · intro i k hik
      change (P i.succ - P i.castSucc) * (P k.succ - P k.castSucc) = 0
      rw [mul_sub, sub_mul, sub_mul]
      rcases lt_or_gt_of_ne hik with h | h
      · have h' : (i : ℕ) < k := h
        rw [hPP' i.succ k.succ (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega), hPP' i.castSucc k.succ (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega),
          hPP' i.succ k.castSucc (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega),
          hPP' i.castSucc k.castSucc (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega), sub_self]
      · have h' : (k : ℕ) < i := h
        rw [hPP k.succ i.succ (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega), hPP k.succ i.castSucc (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega),
          hPP k.castSucc i.succ (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega),
          hPP k.castSucc i.castSucc (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)]
        simp
  have hcomm : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i, X * P i = P i * X) ↔ ∀ i, X * u i = u i * X := by
    intro X
    constructor
    · intro h i
      simp only [u, mul_sub, sub_mul, h]
    · intro h i
      induction i using Fin.induction with
      | zero => simp [hP0]
      | succ i ih =>
        have := h i
        simp only [u, mul_sub, sub_mul, ih] at this
        exact sub_left_injective this
  let G : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {X | (∀ i, X * P i = P i * X) ∧ Formalism.REAL.inG ε X}
      add_mem' := by
        rintro X Y ⟨hX, hX'⟩ ⟨hY, hY'⟩
        refine ⟨fun i => by rw [add_mul, mul_add, hX, hY], ?_⟩
        unfold Formalism.REAL.inG at *
        rw [Matrix.conjTranspose_add, add_mul, mul_add, add_add_add_comm, hX', hY', add_zero]
      zero_mem' := ⟨by simp, by simp [Formalism.REAL.inG]⟩
      smul_mem' := by
        rintro c X ⟨hX, hX'⟩
        refine ⟨fun i => by rw [Matrix.smul_mul, Matrix.mul_smul, hX], ?_⟩
        unfold Formalism.REAL.inG at *
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, hX', smul_zero] }
  have hd := finrank_skew_commutant ε j u hu
    (fun i => by simp only [u, Matrix.conjTranspose_sub, hH])
    (fun i k => by simp only [u, mul_sub, sub_mul, hPJ, sub_self])
    (fun i => by
      simp only [u]
      rw [Matrix.trace_sub, trace_of_proj _ _ (h1 _) (h2 _), trace_of_proj _ _ (h1 _) (h2 _), hrk]
      push_cast
      ring) G (fun X => by rw [← hcomm]; rfl)
  obtain ⟨E, hE, hspan⟩ := exists_orthonormal G _ hd
  refine ⟨(commutant P).restrictScalars ℝ, E, fun X hX Y hY k => ?_, hE, fun X => ?_, ?_⟩
  · rw [mul_assoc, hY k, ← mul_assoc, hX k, mul_assoc]
  · rw [hspan]
    rfl
  · ext g
    change (∀ i, _) ↔ ∀ i, (uMat g - 1) * P i = P i * (uMat g - 1)
    refine forall_congr' fun i => ?_
    rw [keeps_iff_comm (W i) (P i) (hH i) (h1 i) (h2 i), sub_mul, mul_sub, one_mul, mul_one, sub_left_inj]

end GlobalTheory.LeviAlgebra

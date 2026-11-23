import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas.CompactAlg

variable {n : ℕ}

theorem exists_orthonormal (S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (hd : Module.finrank ℝ S = d) :
    ∃ E : Fin d → Matrix (Fin n) (Fin n) ℂ,
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ Submodule.span ℝ (Set.range E) = S := by
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) :=
    { toFun := fun X => WithLp.toLp 2 fun x => X x.1 x.2
      invFun := fun v => Matrix.of fun a b => v (a, b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hin : ∀ X Y, ((X * Yᴴ).trace).re = inner ℝ (e X) (e Y) := by
    intro X Y
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    simp [Matrix.trace, Matrix.mul_apply, e, Complex.inner, mul_comm]
    rfl
  have hd' : Module.finrank ℝ (S.map e.toLinearMap) = d := by
    rw [LinearEquiv.finrank_map_eq, hd]
  let b := (stdOrthonormalBasis ℝ (S.map e.toLinearMap)).reindex (finCongr hd')
  refine ⟨fun i => e.symm (b i), fun i k => ?_, ?_⟩
  · rw [hin, e.apply_symm_apply, e.apply_symm_apply]
    exact orthonormal_iff_ite.1 b.orthonormal i k
  · have h1 : Submodule.span ℝ (Set.range fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) =
        S.map e.toLinearMap := by
      have := congrArg (Submodule.map (S.map e.toLinearMap).subtype) b.toBasis.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
      simpa [Function.comp_def] using this
    have h2 := congrArg (Submodule.map e.symm.toLinearMap) h1
    rw [Submodule.map_span, ← Set.range_comp, ← Submodule.map_comp] at h2
    simpa [Function.comp_def] using h2

def skewPart (B : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | X ∈ B ∧ Xᴴ = -X}
  add_mem' := fun {X Y} hX hY => ⟨B.add_mem hX.1 hY.1, by rw [conjTranspose_add, hX.2, hY.2, neg_add]⟩
  zero_mem' := ⟨B.zero_mem, by simp⟩
  smul_mem' := fun c X hX => ⟨B.smul_of_tower_mem c hX.1, by
    rw [conjTranspose_smul, hX.2]; simp⟩

theorem finrank_skewPart (B : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (hB : ∀ X ∈ B, Xᴴ ∈ B) :
    Module.finrank ℝ (skewPart B) = Module.finrank ℂ B := by
  let f : (skewPart B × skewPart B) →ₗ[ℝ] B :=
    { toFun := fun x => ⟨x.1.1 + Complex.I • x.2.1, B.add_mem x.1.2.1 (B.smul_mem _ x.2.2.1)⟩
      map_add' := fun x y => by
        ext1; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]; abel
      map_smul' := fun c x => by
        ext1
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ h
    have h1 : X + Complex.I • Y = 0 := congrArg Subtype.val h
    have h2 : -X + Complex.I • Y = 0 := by
      have := congrArg conjTranspose h1
      rw [conjTranspose_add, conjTranspose_smul, hX.2, hY.2] at this
      simpa using this
    have h3 : (2 : ℂ) • X = 0 := by
      rw [two_smul]; linear_combination (norm := module) h1 - h2
    have hX0 : X = 0 := by simpa using h3
    have hY0 : Y = 0 := by
      rw [hX0, zero_add] at h1; simpa using h1
    ext1 <;> ext1 <;> assumption
  have hsurj : Function.Surjective f := by
    rintro ⟨X, hX⟩
    refine ⟨(⟨(1 / 2 : ℂ) • (X - Xᴴ), B.smul_mem _ (B.sub_mem hX (hB X hX)), ?_⟩,
      ⟨(-Complex.I / 2 : ℂ) • (X + Xᴴ), B.smul_mem _ (B.add_mem hX (hB X hX)), ?_⟩), ?_⟩
    · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      simp only [one_div, star_inv₀, star_ofNat]; module
    · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
      simp only [star_div₀, star_neg, star_ofNat, Complex.star_def, Complex.conj_I, map_ofNat]; module
    · ext1
      change (1 / 2 : ℂ) • (X - Xᴴ) + Complex.I • (-Complex.I / 2 : ℂ) • (X + Xᴴ) = X
      rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
      module
  have h := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex] at h
  omega

theorem trace_mulLeftRight (A C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ _ (LinearMap.mulLeftRight ℂ (A, C)) = A.trace * C.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.sum_mul_sum,
    Matrix.stdBasis_eq_single, LinearMap.mulLeftRight_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.stdBasis, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ (∀ y, P *ᵥ y ∈ W) ∧ (∀ y ∈ W, P *ᵥ y = y) ∧
      P.trace = Module.finrank ℂ W := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let W' : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := W.map e.toLinearMap
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.toEuclideanLin.symm W'.starProjection.toLinearMap
  have hP : ∀ y, e (P *ᵥ y) = W'.starProjection (e y) := by
    intro y
    have : Matrix.toEuclideanLin P = W'.starProjection.toLinearMap := LinearEquiv.apply_symm_apply _ _
    exact LinearMap.congr_fun this (e y)
  have h1 : ∀ y, P *ᵥ y ∈ W := by
    intro y
    have : e (P *ᵥ y) ∈ W' := by rw [hP]; exact W'.starProjection_apply_mem _
    obtain ⟨z, hz, h⟩ := this
    rwa [← e.injective h]
  have h2 : ∀ y ∈ W, P *ᵥ y = y := by
    intro y hy
    apply e.injective
    rw [hP]
    exact Submodule.starProjection_eq_self_iff.2 ⟨y, hy, rfl⟩
  refine ⟨P, ?_, h1, h2, ?_⟩
  · apply Matrix.isHermitian_iff_isSymmetric.2
    rw [LinearEquiv.apply_symm_apply]
    exact W'.starProjection_isSymmetric
  · have h : LinearMap.IsProj W (Matrix.toLin' P) := ⟨h1, h2⟩
    rw [← h.trace, Matrix.trace_toLin'_eq]

def commutant {κ : Type} (J : Matrix (Fin n) (Fin n) ℂ) (e : κ → Matrix (Fin n) (Fin n) ℂ) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | J * X = X * J ∧ ∀ k, e k * X = X * e k}
  add_mem' := fun {X Y} hX hY => ⟨by rw [mul_add, add_mul, hX.1, hY.1],
    fun k => by rw [mul_add, add_mul, hX.2, hY.2]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := fun c X hX => ⟨by rw [Matrix.mul_smul, Matrix.smul_mul, hX.1],
    fun k => by rw [Matrix.mul_smul, Matrix.smul_mul, hX.2]⟩

theorem finrank_commutant {κ : Type} [Fintype κ] (J : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = 1)
    (e : κ → Matrix (Fin n) (Fin n) ℂ) (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ k, ∃ l, J * e k * J = e l) :
    (Module.finrank ℂ (commutant J e) : ℂ) = (1 / 2 : ℂ) * ∑ k, ((e k).trace ^ 2 + (J * e k).trace ^ 2) := by
  classical
  let π : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (1 / 2 : ℂ) • ∑ k, (LinearMap.mulLeftRight ℂ (e k, e k) + LinearMap.mulLeftRight ℂ (J * e k, e k * J))
  have hπ : ∀ X, π X = (1 / 2 : ℂ) • ((∑ k, e k * X * e k) + J * (∑ k, e k * X * e k) * J) := by
    intro X
    simp only [π, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.mulLeftRight_apply,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by rw [← mul_assoc, hJ, one_mul]
  have hD : ∀ X l, e l * (∑ k, e k * X * e k) = (∑ k, e k * X * e k) * e l := by
    intro X l
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l, Finset.sum_eq_single l]
    · rw [← mul_assoc, ← mul_assoc, (he.idem l).eq, mul_assoc _ (e l), (he.idem l).eq]
    · intro k _ hk
      rw [mul_assoc, he.ortho hk, mul_zero]
    · simp
    · intro k _ hk
      rw [← mul_assoc, ← mul_assoc, he.ortho (Ne.symm hk), zero_mul, zero_mul]
    · simp
  have hP : LinearMap.IsProj (commutant J e) π := by
    constructor
    · intro X
      rw [hπ]
      refine Submodule.smul_mem _ _ ⟨?_, fun k => ?_⟩
      · simp only [mul_add, add_mul, mul_assoc, hJJ, hJ, mul_one]
        rw [add_comm]
      · obtain ⟨l, hl⟩ := hσ k
        have h1 : e k * J = J * e l := by rw [← hl]; simp only [mul_assoc, hJJ]
        have h2 : J * e k = e l * J := by rw [← hl]; simp only [mul_assoc, hJ, mul_one]
        rw [mul_add, add_mul, hD, ← mul_assoc, ← mul_assoc, h1, mul_assoc J, hD, mul_assoc _ J, h2]
        simp only [mul_assoc]
    · intro X hX
      have : ∑ k, e k * X * e k = X := by
        simp_rw [hX.2, mul_assoc, (he.idem _).eq]
        rw [← Finset.mul_sum, he.complete, mul_one]
      rw [hπ, this, hX.1, mul_assoc, hJ, mul_one]
      module
  rw [← hP.trace]
  simp only [π, map_smul, map_sum, map_add, trace_mulLeftRight, smul_eq_mul, Matrix.trace_mul_comm (e _) J, sq]

theorem exists_trace_eq_nat (M : Matrix (Fin n) (Fin n) ℂ) (h : M * M = M) : ∃ m : ℕ, M.trace = m := by
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' M)) (Matrix.toLin' M) :=
    ⟨fun x => ⟨x, rfl⟩, by
      rintro _ ⟨x, rfl⟩
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, h]⟩
  exact ⟨_, by rw [← hp.trace, Matrix.trace_toLin'_eq]⟩

theorem trace_Jm (ε : Fin n → Bool) (p q : ℕ) (hp : (univ.filter fun a => ε a = true).card = p)
    (hq : (univ.filter fun a => ε a = false).card = q) :
    (Formalism.REAL.Jm ε).trace = (p : ℂ) - q ∧ (n : ℂ) = p + q := by
  have h : (univ.filter fun a => ¬ ε a = true) = univ.filter fun a => ε a = false := by simp
  constructor
  · rw [Formalism.REAL.Jm, Matrix.trace_diagonal, Finset.sum_ite, h]
    simp [hp, hq, sub_eq_add_neg]
  · have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
    rw [h, hp, hq, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm

theorem commute_proj_iff (W : Submodule ℂ (Fin n → ℂ)) (P : Matrix (Fin n) (Fin n) ℂ) (h0 : Pᴴ = P)
    (h1 : ∀ y, P *ᵥ y ∈ W) (h2 : ∀ y ∈ W, P *ᵥ y = y) (X : Matrix (Fin n) (Fin n) ℂ) :
    P * X = X * P ↔ ∀ y ∈ W, X *ᵥ y ∈ W ∧ Xᴴ *ᵥ y ∈ W := by
  constructor
  · intro h y hy
    have h' : P * Xᴴ = Xᴴ * P := by
      have := congrArg conjTranspose h
      rw [conjTranspose_mul, conjTranspose_mul, h0] at this
      exact this.symm
    constructor
    · rw [← h2 y hy, mulVec_mulVec, ← h, ← mulVec_mulVec]; exact h1 _
    · rw [← h2 y hy, mulVec_mulVec, ← h', ← mulVec_mulVec]; exact h1 _
  · intro h
    have a1 : P * (X * P) = X * P := Matrix.ext_iff_mulVec.2 fun y => by
      rw [← mulVec_mulVec, ← mulVec_mulVec]; exact h2 _ (h _ (h1 y)).1
    have a2 : P * (Xᴴ * P) = Xᴴ * P := Matrix.ext_iff_mulVec.2 fun y => by
      rw [← mulVec_mulVec, ← mulVec_mulVec]; exact h2 _ (h _ (h1 y)).2
    have a3 := congrArg conjTranspose a2
    simp only [conjTranspose_mul, h0, conjTranspose_conjTranspose, mul_assoc] at a3
    rw [← a3, a1]

theorem half_idem (J R : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = 1) (hJR : J * R = R * J) (hRR : R * R = R)
    (s : ℂ) (hs : s * s = 1) :
    ((1 / 2 : ℂ) • (R + s • (J * R))) * ((1 / 2 : ℂ) • (R + s • (J * R))) = (1 / 2 : ℂ) • (R + s • (J * R)) := by
  have b1 : R * (J * R) = J * R := by rw [← mul_assoc, ← hJR, mul_assoc, hRR]
  have b2 : J * R * R = J * R := by rw [mul_assoc, hRR]
  have b3 : J * R * (J * R) = R := by rw [mul_assoc, b1, ← mul_assoc, hJ, one_mul]
  rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, b1, b2, b3, hRR, smul_smul s s, hs]
  module

theorem exists_flag_algebra (ε : Fin n → Bool) {a : ℕ} (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (hW : IsIsoFlag ε j W) (p q : ℕ)
    (hp : (univ.filter fun a => ε a = true).card = p) (hq : (univ.filter fun a => ε a = false).card = q) :
    ∃ B : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ B ↔ Formalism.REAL.Jm ε * X = X * Formalism.REAL.Jm ε ∧ ∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i ∧ Xᴴ *ᵥ y ∈ W i) ∧
      Module.finrank ℂ B = (p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2 := by
  obtain ⟨hW0, hmono, hrk, hiso⟩ := hW
  obtain ⟨htJ, hn⟩ := trace_Jm ε p q hp hq
  have hJ := Formalism.REAL.Jm_mul_self ε
  set J := Formalism.REAL.Jm ε with hJdef
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by rw [← mul_assoc, hJ, one_mul]
  choose P hP0 hP1 hP2 hPt using fun i => exists_proj (W i)
  have hPP : ∀ i k, i ≤ k → P k * P i = P i := fun i k h => Matrix.ext_iff_mulVec.2 fun y => by
    rw [← mulVec_mulVec]; exact hP2 k _ (hmono h (hP1 i y))
  have hPP' : ∀ i k, i ≤ k → P i * P k = P i := fun i k h => by
    have := congrArg conjTranspose (hPP i k h)
    rwa [conjTranspose_mul, hP0, hP0] at this
  have hPJ : ∀ i k, P i * (J * P k) = 0 := fun i k => by
    ext r s
    have := hiso _ (hmono (Fin.le_last i) (hP1 i (Pi.single r 1))) _
      (hmono (Fin.le_last k) (hP1 k (Pi.single s 1)))
    rw [star_mulVec, hP0, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, mul_assoc] at this
    simpa [← Pi.single_star] using this
  have hPz : P 0 = 0 := Matrix.ext_iff_mulVec.2 fun y => by
    have := hP1 0 y
    rw [hW0] at this
    simpa using this
  let Q : Fin a → Matrix (Fin n) (Fin n) ℂ := fun i => P i.succ - P i.castSucc
  have hQJ : ∀ i k, Q i * (J * Q k) = 0 := fun i k => by
    simp only [Q, mul_sub, sub_mul, hPJ, sub_zero]
  have hQQ : ∀ i, Q i * Q i = Q i := fun i => by
    have h : i.castSucc ≤ i.succ := (Fin.castSucc_lt_succ).le
    simp only [Q, mul_sub, sub_mul, hPP _ _ le_rfl, hPP _ _ h, hPP' _ _ h, sub_self, sub_zero]
  have hQQ' : ∀ i k, i ≠ k → Q i * Q k = 0 := fun i k hik => by
    rcases lt_or_gt_of_ne hik with h | h
    · have h1 : i.succ ≤ k.castSucc := Fin.succ_le_castSucc_iff.2 h
      have h2 : i.succ ≤ k.succ := Fin.succ_le_succ_iff.2 h.le
      have h3 : i.castSucc ≤ k.castSucc := Fin.castSucc_le_castSucc_iff.2 h.le
      have h4 : i.castSucc ≤ k.succ := h3.trans (Fin.castSucc_lt_succ).le
      simp only [Q, mul_sub, sub_mul, hPP' _ _ h1, hPP' _ _ h2, hPP' _ _ h3, hPP' _ _ h4, sub_self]
    · have h1 : k.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.2 h
      have h2 : k.succ ≤ i.succ := Fin.succ_le_succ_iff.2 h.le
      have h3 : k.castSucc ≤ i.castSucc := Fin.castSucc_le_castSucc_iff.2 h.le
      have h4 : k.castSucc ≤ i.succ := h3.trans (Fin.castSucc_lt_succ).le
      simp only [Q, mul_sub, sub_mul, hPP _ _ h1, hPP _ _ h2, hPP _ _ h3, hPP _ _ h4, sub_self]
  have hQt : ∀ i, (Q i).trace = j i := fun i => by
    simp only [Q, Matrix.trace_sub, hPt, hrk]; push_cast; ring
  have hQJt : ∀ i, (J * Q i).trace = 0 := fun i => by
    rw [← hQQ, ← mul_assoc, Matrix.trace_mul_comm, hQJ, Matrix.trace_zero]
  let e₀ : Fin a ⊕ Fin a → Matrix (Fin n) (Fin n) ℂ := Sum.elim Q fun i => J * (Q i * J)
  have he₀ : OrthogonalIdempotents e₀ := by
    constructor
    · rintro (i | i)
      · exact hQQ i
      · change J * (Q i * J) * (J * (Q i * J)) = J * (Q i * J)
        simp only [mul_assoc, hJJ]
        rw [← mul_assoc (Q i), hQQ]
    · rintro (i | i) (k | k) hik
      · exact hQQ' i k (fun h => hik (by rw [h]))
      · change Q i * (J * (Q k * J)) = 0
        rw [← mul_assoc J, ← mul_assoc, hQJ, zero_mul]
      · change J * (Q i * J) * Q k = 0
        simp only [mul_assoc, hQJ, mul_zero]
      · change J * (Q i * J) * (J * (Q k * J)) = 0
        simp only [mul_assoc, hJJ]
        rw [← mul_assoc (Q i), hQQ' i k (fun h => hik (by rw [h])), zero_mul, mul_zero]
  have he := CompleteOrthogonalIdempotents.option he₀
  set R : Matrix (Fin n) (Fin n) ℂ := 1 - ∑ i, e₀ i with hR
  have hR' : R = 1 - (∑ i, Q i + ∑ i, J * (Q i * J)) := by rw [hR, Fintype.sum_sum_type]; rfl
  have hJR : J * R = R * J := by
    simp only [hR', mul_sub, sub_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc, hJJ, hJ,
      mul_one, one_mul]
    rw [add_comm]
  have hRR : R * R = R := he.idem none
  have ht2 : ∀ i, (J * (Q i * J)).trace = j i := fun i => by
    rw [Matrix.trace_mul_comm, mul_assoc, hJ, mul_one, hQt]
  have ht3 : ∀ i, (J * (J * (Q i * J))).trace = 0 := fun i => by
    rw [hJJ, Matrix.trace_mul_comm, hQJt]
  have hRt : R.trace = p + q - 2 * ((∑ i, j i : ℕ) : ℂ) := by
    simp only [hR', Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum, hQt, ht2, Matrix.trace_one,
      Fintype.card_fin, hn]
    push_cast; ring
  have hJRt : (J * R).trace = p - q := by
    simp only [hR', mul_sub, mul_add, Finset.mul_sum, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum,
      hQJt, ht3, mul_one, htJ]
    simp
  have hle : ∀ s : ℂ, s * s = 1 → ∃ m : ℕ, (1 / 2 : ℂ) * (R.trace + s * (J * R).trace) = m := by
    intro s hs
    obtain ⟨m, hm⟩ := exists_trace_eq_nat _ (half_idem J R hJ hJR hRR s hs)
    exact ⟨m, by simpa [mul_add] using hm⟩
  have hjp : ∑ i, j i ≤ p := by
    obtain ⟨m, hm⟩ := hle 1 (by ring)
    rw [hRt, hJRt] at hm
    have : (p : ℂ) = ((∑ i, j i + m : ℕ) : ℂ) := by rw [Nat.cast_add]; linear_combination hm
    have := Nat.cast_injective this
    omega
  have hjq : ∑ i, j i ≤ q := by
    obtain ⟨m, hm⟩ := hle (-1) (by ring)
    rw [hRt, hJRt] at hm
    have : (q : ℂ) = ((∑ i, j i + m : ℕ) : ℂ) := by rw [Nat.cast_add]; linear_combination hm
    have := Nat.cast_injective this
    omega
  refine ⟨commutant J (fun o : Option (Fin a ⊕ Fin a) => o.elim R e₀), fun X => ?_, ?_⟩
  · refine and_congr_right fun hX => ?_
    simp_rw [← fun i => commute_proj_iff (W i) (P i) (hP0 i) (hP1 i) (hP2 i) X]
    constructor
    · intro h i
      induction i using Fin.induction with
      | zero => simp [hPz]
      | succ i ih =>
        have : Q i * X = X * Q i := h (some (Sum.inl i))
        simp only [Q, sub_mul, mul_sub, ih] at this
        exact sub_left_injective this
    · intro h
      have c1 : ∀ i, Q i * X = X * Q i := fun i => by simp only [Q, sub_mul, mul_sub, h]
      have c2 : ∀ i, J * (Q i * J) * X = X * (J * (Q i * J)) := fun i => by
        rw [mul_assoc, mul_assoc, hX, ← mul_assoc (Q i), c1, mul_assoc X, ← mul_assoc J, hX, mul_assoc]
      rintro (_ | i | i)
      · change R * X = X * R
        simp only [hR', sub_mul, mul_sub, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, c1, c2, one_mul,
          mul_one]
      · exact c1 i
      · exact c2 i
  · have h := finrank_commutant J hJ _ he (by
      rintro (_ | i | i)
      · exact ⟨none, by change J * R * J = R; rw [hJR, mul_assoc, hJ, mul_one]⟩
      · exact ⟨some (Sum.inr i), mul_assoc _ _ _⟩
      · exact ⟨some (Sum.inl i), by
          change J * (J * (Q i * J)) * J = Q i; rw [hJJ, mul_assoc, hJ, mul_one]⟩)
    rw [Fintype.sum_option, Fintype.sum_sum_type] at h
    simp only [Option.elim, e₀, Sum.elim_inl, Sum.elim_inr, hQt, hQJt, ht2, ht3, hRt, hJRt] at h
    apply Nat.cast_injective (R := ℂ)
    refine h.trans ?_
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hjp, Nat.cast_sub hjq,
      Nat.cast_sum (f := fun i => j i ^ 2)]
    simp only [Nat.cast_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    ring

theorem exists_algebra_inter (ε : Fin n → Bool) {a : ℕ} (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (hW : IsIsoFlag ε j W) (p q : ℕ)
    (hp : (univ.filter fun a => ε a = true).card = p) (hq : (univ.filter fun a => ε a = false).card = q) :
    ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
      (E : Fin ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) → Matrix (Fin n) (Fin n) ℂ),
      (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧
      (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧
      maxK ε ∩ flagM ε W = {g | uMat g - 1 ∈ A} := by
  obtain ⟨B, hB, hd⟩ := exists_flag_algebra ε j W hW p q hp hq
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJs := Formalism.REAL.Jm_conjTranspose ε
  have hstar : ∀ X ∈ B, Xᴴ ∈ B := by
    intro X hX
    rw [hB] at hX ⊢
    refine ⟨?_, fun i y hy => ⟨(hX.2 i y hy).2, by simpa using (hX.2 i y hy).1⟩⟩
    have := congrArg conjTranspose hX.1
    rw [conjTranspose_mul, conjTranspose_mul, hJs] at this
    exact this.symm
  obtain ⟨E, hE, hsp⟩ := exists_orthonormal (skewPart B) _ ((finrank_skewPart B hstar).trans hd)
  refine ⟨B.restrictScalars ℝ, E, ?_, hE, ?_, ?_⟩
  · intro X hX Y hY
    rw [Submodule.restrictScalars_mem, hB] at hX hY ⊢
    refine ⟨by rw [← mul_assoc, hX.1, mul_assoc, hY.1, mul_assoc], fun i y hy => ⟨?_, ?_⟩⟩
    · rw [← mulVec_mulVec]; exact (hX.2 i _ (hY.2 i y hy).1).1
    · rw [conjTranspose_mul, ← mulVec_mulVec]; exact (hY.2 i _ (hX.2 i y hy).2).2
  · intro X
    rw [hsp]
    refine and_congr_right fun hX => ?_
    have h1 := ((hB X).1 hX).1
    rw [Formalism.REAL.inG, h1, ← add_mul]
    constructor
    · intro h
      have := congrArg (· * Formalism.REAL.Jm ε) h
      simp only [mul_assoc, hJ, mul_one, zero_mul] at this
      exact eq_neg_of_add_eq_zero_left this
    · intro h; rw [h]; simp
  · ext g
    have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ B := by
      rw [hB]; exact ⟨by simp, fun i y hy => by simpa using hy⟩
    have h2 : uMat g - 1 ∈ B ↔ uMat g ∈ B :=
      ⟨fun h => by simpa using B.add_mem h h1, fun h => B.sub_mem h h1⟩
    have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
    change _ ↔ uMat g - 1 ∈ B
    rw [h2, hB]
    refine and_congr_left fun _ => ?_
    change (uMat g)ᴴ * uMat g = 1 ↔ _
    constructor
    · intro h
      have h' := mul_eq_one_comm.1 h
      conv_rhs => rw [← hg, ← mul_assoc, ← mul_assoc, h', one_mul]
    · intro h
      rw [mul_assoc, h, ← mul_assoc] at hg
      have := congrArg (· * Formalism.REAL.Jm ε) hg
      simpa only [mul_assoc, hJ, mul_one] using this

theorem compact_algebras : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → (∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (p ^ 2 + q ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ maxK ε = {g | uMat g - 1 ∈ A}) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ maxK ε ∩ flagM ε W = {g | uMat g - 1 ∈ A} := by
  intro n ε a j W hW p q hp hq
  refine ⟨?_, exists_algebra_inter ε j W hW p q hp hq⟩
  have h0 : IsIsoFlag ε (a := 0) (fun _ => 0) (fun _ => ⊥) :=
    ⟨rfl, monotone_const, fun i => i.elim0, fun x hx y _ => by
      rw [(Submodule.mem_bot ℂ).1 hx]; simp⟩
  obtain ⟨A, E, h1, h2, h3, h4⟩ := exists_algebra_inter ε _ _ h0 p q hp hq
  refine ⟨A, E, h1, h2, h3, ?_⟩
  rw [← h4]
  symm
  refine Set.inter_eq_left.2 fun g _ i y hy => ?_
  rw [(Submodule.mem_bot ℂ).1 hy]; simp

end GlobalTheory.FlagMeas.CompactAlg

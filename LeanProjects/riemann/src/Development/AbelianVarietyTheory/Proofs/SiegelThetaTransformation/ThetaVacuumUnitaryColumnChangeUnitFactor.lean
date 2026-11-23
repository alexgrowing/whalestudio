import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledVacuumEqHermitianCharacter
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColVac

theorem exists_unit_factor {P : Type} (A B : P → ℂ)
    (h : ∀ p q, B p * conj (B q) = A p * conj (A q)) : ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ p, B p = t * A p := by
  by_cases hA : ∀ p, A p = 0
  · refine ⟨1, by simp, fun p => ?_⟩
    have hp := h p p
    rw [hA p, zero_mul, Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at hp
    rw [hp, hA p, mul_zero]
  simp only [not_forall] at hA
  obtain ⟨p₀, hp₀⟩ := hA
  have e₀ := h p₀ p₀
  have hn : ‖B p₀‖ = ‖A p₀‖ := by
    have := congrArg (fun c : ℂ => ‖c‖) e₀
    simp only [norm_mul, Complex.norm_conj] at this
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp this
  have hB₀ : B p₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, hn, norm_ne_zero_iff]
    exact hp₀
  refine ⟨B p₀ / A p₀, by rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hp₀)], fun p => ?_⟩
  have e₁ := h p p₀
  have key : B p * A p₀ = B p₀ * A p := by
    apply mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hB₀)
    linear_combination (A p₀) * e₁ - (A p) * e₀
  rw [div_mul_eq_mul_div, eq_div_iff hp₀, key]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

omit [IsCMField E] in

theorem mul_mem_tens_of_moves {Λ Λ' : Lt E n} {K : Lt E r} {h : Matrix (Fin n) (Fin n) E}
    (m : Moves h Λ Λ') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ K) : h * y ∈ tens Λ' K := by
  unfold tens at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨h *ᵥ v, (m v).1 hv, u, hu, Matrix.mul_vecMulVec h v u⟩
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg]; exact neg_mem ha

theorem mul_mem_tens_iff {Λ Λ' : Lt E n} {K : Lt E r} {h : Matrix (Fin n) (Fin n) E}
    (hu : ccT h * h = 1) (m : Moves h Λ Λ') (y : Matrix (Fin n) (Fin r) E) :
    h * y ∈ tens Λ' K ↔ y ∈ tens Λ K := by
  have hh : h * ccT h = 1 := mul_eq_one_comm.mp hu
  have m' : Moves (ccT h) Λ' Λ := fun v => by
    rw [m (ccT h *ᵥ v), Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]
  constructor
  · intro hy
    have := mul_mem_tens_of_moves m' hy
    rwa [← Matrix.mul_assoc, hu, Matrix.one_mul] at this
  · intro hy
    exact mul_mem_tens_of_moves m hy

theorem trace_mul_unitary {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (β : Matrix (Fin r) (Fin r) E) (y : Matrix (Fin n) (Fin r) E) :
    (h * y * β * ccT (h * y)).trace = (y * β * ccT y).trace := by
  have hc : ccT (h * y) = ccT y * ccT h := by
    ext i j
    simp only [ccT, cc, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hc, ← Matrix.mul_assoc, Matrix.trace_mul_comm (h * y * β * ccT y) (ccT h)]
  simp only [← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem isSB_smul {φ : TF n g} (hφ : IsSB φ) (c : ℂ) : IsSB (c • φ) := by
  obtain ⟨R, hR, hl⟩ := hφ
  refine ⟨R, hR, fun x hx => hl.1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, h0, mul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, hl.2 x y hy]

variable (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r)

theorem dblz_hAct (h : Matrix (Fin n) (Fin n) E) (x₁ x₂ : Frame X.Ψ r) (z₁ z₂ : Fin n → Fin g → ℂ) (τ : X.Ψ) :
    dblz X idx x₁ x₂ (Dict.hAct X idx h z₁) (fun k i => conj (Dict.hAct X idx h z₂ k i)) τ =
      (h.map τ.1)ᴴᵀ * dblz X idx x₁ x₂ z₁ (fun k i => conj (z₂ k i)) τ := by
  have hv : ∀ k, (fun a : Fin r => if (a : ℕ) < X.p0 then Dict.hAct X idx h z₁ k (idx.symm (τ, a))
      else conj (Dict.hAct X idx h z₂ k (idx.symm (τ, a)))) =
      ∑ k', conj (τ.1 (h k k')) • (fun a : Fin r => if (a : ℕ) < X.p0 then z₁ k' (idx.symm (τ, a))
        else conj (z₂ k' (idx.symm (τ, a)))) := by
    intro k
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Dict.hAct, Equiv.apply_symm_apply]
    split_ifs with ha
    · rw [rowType_of_lt X τ ha]
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    · rw [rowType_of_le X τ (not_lt.mp ha)]
      simp only [map_sum, map_mul]
  ext k b
  simp only [dblz, Matrix.of_apply, hv, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dblz'_hAct (h : Matrix (Fin n) (Fin n) E) (x₁ x₂ : Frame X.Ψ r) (z₁ z₂ : Fin n → Fin g → ℂ) (τ : X.Ψ) :
    dblz' X idx x₁ x₂ (Dict.hAct X idx h z₁) (fun k i => conj (Dict.hAct X idx h z₂ k i)) τ =
      h.map τ.1 * dblz' X idx x₁ x₂ z₁ (fun k i => conj (z₂ k i)) τ := by
  have hv : ∀ k, (fun a : Fin r => if (a : ℕ) < X.p0 then conj (Dict.hAct X idx h z₂ k (idx.symm (τ, a)))
      else Dict.hAct X idx h z₁ k (idx.symm (τ, a))) =
      ∑ k', τ.1 (h k k') • (fun a : Fin r => if (a : ℕ) < X.p0 then conj (z₂ k' (idx.symm (τ, a)))
        else z₁ k' (idx.symm (τ, a))) := by
    intro k
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Dict.hAct, Equiv.apply_symm_apply]
    split_ifs with ha
    · rw [rowType_of_lt X τ ha]
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, map_sum, map_mul, Complex.conj_conj]
    · rw [rowType_of_le X τ (not_lt.mp ha)]
  ext k b
  simp only [dblz', Matrix.of_apply, hv, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.sum_vecMul,
    Matrix.smul_vecMul, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sum_rows_eq_trace (a b : Matrix (Fin n) (Fin r) ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    ∑ k, a k ⬝ᵥ M *ᵥ b k = (a * M * bᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem map_unitary {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (τ : E →+* ℂ) :
    (h.map τ)ᴴ * h.map τ = 1 := by
  have hc : (h.map τ)ᴴ = (ccT h).map τ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, ccT, Matrix.transpose_apply, cc,
      NumberField.IsCMField.complexEmbedding_complexConj, Complex.star_def]
  rw [hc, ← Matrix.map_mul, hu]
  exact Matrix.map_one _ (map_zero τ) (map_one τ)

private theorem sum_unitary_mul_dotProduct_mulVec_eq (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ * H = 1) (a b : Matrix (Fin n) (Fin r) ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) : ∑ k, (H * a) k ⬝ᵥ M *ᵥ (Hᴴᵀ * b) k = ∑ k, a k ⬝ᵥ M *ᵥ b k := by
  rw [sum_rows_eq_trace, sum_rows_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (H * a * M * bᵀ) Hᴴ]
  simp only [← Matrix.mul_assoc, hH, Matrix.one_mul]

theorem kZero_hAct {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (x₁ x₂ : Frame X.Ψ r)
    (z₁ z₂ : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ (Dict.hAct X idx h z₁) (fun k i => conj (Dict.hAct X idx h z₂ k i)) =
      kZero X idx x₁ x₂ z₁ (fun k i => conj (z₂ k i)) := by
  simp only [kZero, dblz_hAct, dblz'_hAct]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [sum_unitary_mul_dotProduct_mulVec_eq _ (map_unitary hu τ.1)]

private theorem sum_quadratic_linear_unitary_mul_rows_eq (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ * H = 1) (Y D D' : Matrix (Fin n) (Fin r) ℂ)
    (Zm : Matrix (Fin r) (Fin r) ℂ) :
    ∑ k, ((H * Y) k ⬝ᵥ Zm *ᵥ (H * Y)ᴴᵀ k + (H * Y) k ⬝ᵥ (Hᴴᵀ * D) k + (H * D') k ⬝ᵥ (H * Y)ᴴᵀ k) =
      ∑ k, (Y k ⬝ᵥ Zm *ᵥ Yᴴᵀ k + Y k ⬝ᵥ D k + D' k ⬝ᵥ Yᴴᵀ k) := by
  have t1 := sum_unitary_mul_dotProduct_mulVec_eq H hH Y Yᴴᵀ Zm
  have t2 := sum_unitary_mul_dotProduct_mulVec_eq H hH Y D 1
  have t3 := sum_unitary_mul_dotProduct_mulVec_eq H hH D' Yᴴᵀ 1
  simp only [Matrix.one_mulVec] at t2 t3
  rw [Matrix.conjTranspose_mul, Matrix.transpose_mul, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, t1, t2, t3]

private theorem thH_unitary_translate_eq {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    {ψ ψ' : Matrix (Fin n) (Fin r) E → ℂ} (e : ∀ y, ψ' (h * y) = ψ y) (Z : CM X.Ψ r r) (D D' : CM X.Ψ n r) :
    thH X.Ψ ψ' Z (fun τ => (h.map τ.1)ᴴᵀ * D τ) (fun τ => h.map τ.1 * D' τ) = thH X.Ψ ψ Z D D' := by
  have hh : h * ccT h = 1 := mul_eq_one_comm.mp hu
  let eqv : Matrix (Fin n) (Fin r) E ≃ Matrix (Fin n) (Fin r) E :=
    { toFun := fun y => h * y
      invFun := fun y => ccT h * y
      left_inv := fun y => by simp only [← Matrix.mul_assoc, hu, Matrix.one_mul]
      right_inv := fun y => by simp only [← Matrix.mul_assoc, hh, Matrix.one_mul] }
  unfold thH
  rw [← eqv.tsum_eq]
  refine tsum_congr fun y => ?_
  change ψ' (h * y) * _ = _
  rw [e y]
  congr 3
  unfold expo
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := sum_quadratic_linear_unitary_mul_rows_eq (h.map τ.1) (map_unitary hu τ.1) (y.map τ.1) (D τ) (D' τ) (Z τ)
  rw [← Matrix.map_mul] at this
  exact this

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

theorem prod_hAct {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) {φ₁ φ₂ φ₁' φ₂' : TF n g}
    {ψ ψ' : Matrix (Fin n) (Fin r) E → ℂ} (d : IsDbl X bas idx φ₁ φ₂ ψ) (d' : IsDbl X bas idx φ₁' φ₂' ψ')
    (e : ∀ y, ψ' (h * y) = ψ y) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (z₁ z₂ : Fin n → Fin g → ℂ) :
    thA X bas idx φ₁' x₁ (Dict.hAct X idx h z₁) * conj (thA X bas idx φ₂' x₂ (Dict.hAct X idx h z₂)) =
      thA X bas idx φ₁ x₁ z₁ * conj (thA X bas idx φ₂ x₂ z₂) := by
  have h1 := d' x₁ h₁ x₂ h₂ (Dict.hAct X idx h z₁) (fun k i => conj (Dict.hAct X idx h z₂ k i))
  have h2 := d x₁ h₁ x₂ h₂ z₁ (fun k i => conj (z₂ k i))
  simp only [Complex.conj_conj] at h1 h2
  rw [h1, h2, kZero_hAct X idx hu x₁ x₂ z₁ z₂]
  congr 1
  rw [show dblz X idx x₁ x₂ (Dict.hAct X idx h z₁) (fun k i => conj (Dict.hAct X idx h z₂ k i)) =
      fun τ => (h.map τ.1)ᴴᵀ * dblz X idx x₁ x₂ z₁ (fun k i => conj (z₂ k i)) τ from
      funext (dblz_hAct X idx h x₁ x₂ z₁ z₂),
    show dblz' X idx x₁ x₂ (Dict.hAct X idx h z₁) (fun k i => conj (Dict.hAct X idx h z₂ k i)) =
      fun τ => h.map τ.1 * dblz' X idx x₁ x₂ z₁ (fun k i => conj (z₂ k i)) τ from
      funext (dblz'_hAct X idx h x₁ x₂ z₁ z₂)]
  exact thH_unitary_translate_eq X hu e _ _ _

end GlobalTheory.Dict.ColVac

theorem GlobalTheory.Dict.thA_vacuum_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, Moves h Λ Λ' → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 h hu Λ hΛ Λ' hΛ' m
  have sbP : ∀ (Λ₀ : Lt E n) (L : Lt E r) (v : TF n g), IsSB v →
      IsSB (unitv (projA X bas w (tens Λ₀ L) v)) := by
    intro Λ₀ L v hv
    unfold unitv projA
    refine GlobalTheory.Dict.ColVac.isSB_smul (GlobalTheory.Dict.ColVac.isSB_smul ?_ _) _
    refine finsum_mem_induction (fun φ : TF n g => IsSB φ) GlobalTheory.SW.isSB_zero
      (fun a b ha hb => GlobalTheory.SW.DblVac.sb_add ha hb) ?_
    rintro _ ⟨y, -, rfl⟩
    exact GlobalTheory.SW.TensVac.rho_sb idx hs hn y hv
  let P := {p : Lt E r × TF n g × Frame X.Ψ r × (Fin n → Fin g → ℂ) //
    SelfD X p.1 ∧ IsVac X bas w (tens (stdL E n) p.1) p.2.1 ∧ p.2.2.1 ∈ X.dom}
  let A : P → ℂ := fun p =>
    thA X bas idx (unitv (projA X bas w (tens Λ p.1.1) p.1.2.1)) p.1.2.2.1 p.1.2.2.2
  let B : P → ℂ := fun p =>
    thA X bas idx (unitv (projA X bas w (tens Λ' p.1.1) p.1.2.1)) p.1.2.2.1 (hAct X idx h p.1.2.2.2)
  obtain ⟨t, ht, hBA⟩ := GlobalTheory.Dict.ColVac.exists_unit_factor A B (by
    rintro ⟨⟨L₁, v₁, x₁, z₁⟩, hL₁, hv₁, hx₁⟩ ⟨⟨L₂, v₂, x₂, z₂⟩, hL₂, hv₂, hx₂⟩
    obtain ⟨β, c, -, hβ⟩ := GlobalTheory.SW.dbl_vacuum E r X g bas idx n hs hn w hw hw1 L₁ L₂ hL₁ hL₂ 1 one_pos
      v₁ v₂ hv₁ hv₂
    have d := (GlobalTheory.SW.DblEx.dbl_spec E r X g bas idx n hs hn _ _ (sbP Λ L₁ v₁ hv₁.1)
      (sbP Λ L₂ v₂ hv₂.1)).2.1
    have d' := (GlobalTheory.SW.DblEx.dbl_spec E r X g bas idx n hs hn _ _ (sbP Λ' L₁ v₁ hv₁.1)
      (sbP Λ' L₂ v₂ hv₂.1)).2.1
    refine GlobalTheory.Dict.ColVac.prod_hAct X idx bas hu d d' (fun y => ?_) hx₁ hx₂ z₁ z₂
    rw [hβ Λ' hΛ', hβ Λ hΛ, GlobalTheory.Dict.ColVac.mul_mem_tens_iff hu m, GlobalTheory.Dict.ColVac.trace_mul_unitary hu])
  exact ⟨t, ht, fun L hL v hv x hx z => hBA ⟨(L, v, x, z), hL, hv, hx⟩⟩

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PerMove

open scoped ComplexConjugate

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
lemma _root_.GlobalTheory.PerMove.differentiable_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}
    (M : X → Matrix (Fin r) (Fin r) ℂ) (hM : ∀ a b, Differentiable ℂ fun x => M x a b) :
    Differentiable ℂ fun x => (M x).det := by
  simp only [Matrix.det_apply]
  fun_prop

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
lemma _root_.GlobalTheory.PerMove.inv_mulVec_apply {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (a : Fin r) :
    (A⁻¹ *ᵥ w) a = (A.det)⁻¹ * (A.updateCol a w).det := by
  rw [Matrix.inv_def, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in

lemma _root_.GlobalTheory.PerMove.det_of_triangular {n α : Type*} [Fintype n] [DecidableEq n] [LinearOrder α] (f : n → α)
    (hf : Function.Injective f) (M : Matrix n n ℂ) (hM : ∀ k l, f l < f k → M k l = 0) :
    M.det = ∏ k, M k k := by
  letI : LinearOrder n := LinearOrder.lift' f hf
  exact Matrix.det_of_upperTriangular fun k l h => hM k l h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
lemma _root_.GlobalTheory.PerMove.map_cc (τ : E →+* ℂ) (z : E) : τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc z) = conj (τ z) :=
  NumberField.IsCMField.complexEmbedding_complexConj (K := E) τ z

omit [NumberField E] [IsCMField E] in
lemma hermC_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    FD.hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp [FD.hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma hermC_eq_dotProduct' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma hermC_mulVec_mulVec' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (P *ᵥ u) (P *ᵥ w) = u ⬝ᵥ ((Pᵀ * G.map τ * P.map (starRingEnd ℂ)) *ᵥ star w) := by
  have hstar : star (P *ᵥ w) = P.map (starRingEnd ℂ) *ᵥ star w := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hermC_eq_dotProduct', hstar, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
lemma _root_.GlobalTheory.PerMove.hermC_unitary (τ : E →+* ℂ) (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ u) (γ *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G u v) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w := by
  have hM : γᵀ * G * γ.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc = G := by
    ext a b
    have h := hγ (Pi.single a 1) (Pi.single b 1)
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one] at h
    simp [Pi.single_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc] at h
    simp [Matrix.mul_apply, Finset.sum_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_comm]
    convert h using 3 <;> ring_nf
  have hconj : (γ.map τ).map (starRingEnd ℂ) = (γ.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc).map τ := by
    ext i j
    simp [_root_.GlobalTheory.PerMove.map_cc]
  rw [hermC_mulVec_mulVec', hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hM,
    hermC_eq_dotProduct']

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.PerMove.emb_mulVec (τ : E →+* ℂ) (γ : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (γ *ᵥ v) = γ.map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  ext a
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum]

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
lemma _root_.GlobalTheory.PerMove.col_mul (g x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (g * x) a = g *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a := by
  ext i
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.PerMove.hermC_col_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x b : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (x * b) a) w = ∑ c, b c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x c) w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.PerMove.bor_tri {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.PerMove.bor_diag_ne {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ)
    (a : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ a a ≠ 0 := by
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (_root_.GlobalTheory.PerMove.bor_tri hb τ)] at h
  exact Finset.prod_ne_zero_iff.mp h a (Finset.mem_univ a)

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.PerMove.bor_inv_tri {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹.BlockTriangular id := by
  letI := (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (hb τ).1)
  exact Matrix.blockTriangular_inv_of_blockTriangular (_root_.GlobalTheory.PerMove.bor_tri hb τ)

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.PerMove.bor_inv_diag {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ)
    (a : Fin r) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ a a = (b τ a a)⁻¹ := by
  set M := _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ with hM
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr (hb τ).1)
  have h := congrFun (congrFun hmul a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a] at h
  · have hd : M a a = b τ a a := rfl
    rw [← hd]
    exact eq_inv_of_mul_eq_one_right h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hlt
    · rw [show M a k = 0 from _root_.GlobalTheory.PerMove.bor_tri hb τ hlt, zero_mul]
    · rw [show M⁻¹ k a = 0 from _root_.GlobalTheory.PerMove.bor_inv_tri hb τ hlt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
lemma _root_.GlobalTheory.PerMove.rmul_mem_GG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ}
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G q) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G q := by
  intro τ
  have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · have h := (hx τ).2 i
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin at h ⊢
    rw [hmat, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (_root_.GlobalTheory.PerMove.bor_tri hb τ)]
    set z := ∏ j, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
    have hz : z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => _root_.GlobalTheory.PerMove.bor_diag_ne hb τ _
    have hre : ∀ m : ℂ, (z * m * (starRingEnd ℂ) z).re = Complex.normSq z * m.re := by
      intro m
      rw [mul_right_comm, Complex.mul_conj, Complex.re_ofReal_mul]
    rw [hre, mul_left_comm]
    exact mul_pos (Complex.normSq_pos.mpr hz) h

end GlobalTheory.PerMove

namespace GlobalTheory

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma differentiable_hermC_col_mat {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E)
    (σ : Ψ) (a : Fin r) (w : Fin r → ℂ) :
    Differentiable ℂ fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC σ.1 G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x σ) a) w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC _root_.ReciprocityTheory.ChartRestriction.G.FD.col _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  simp only [Matrix.of_apply]
  fun_prop

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma differentiableOn_mat_inv_mulVec_apply {Ψ : Finset (E →+* ℂ)} (s : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r))
    (hs : ∀ x ∈ s, ∀ σ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x σ).det ≠ 0) (σ : Ψ) (a : Fin r) (w : Fin r → ℂ) :
    DifferentiableOn ℂ (fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x σ)⁻¹ *ᵥ w) a) s := by
  simp only [_root_.GlobalTheory.PerMove.inv_mulVec_apply]
  refine DifferentiableOn.mul ?_ ?_
  · refine DifferentiableOn.inv ?_ fun x hx => hs x hx σ
    refine (_root_.GlobalTheory.PerMove.differentiable_det _ fun i j => ?_).differentiableOn
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat; simp only [Matrix.of_apply]; fun_prop
  · refine (_root_.GlobalTheory.PerMove.differentiable_det _ fun i j => ?_).differentiableOn
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    split_ifs <;> fun_prop

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
private lemma sum_ite_fst_eq_sum_symm {Ψ : Finset (E →+* ℂ)} [DecidableEq Ψ] {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (σ : Ψ)
    (F : Fin g → ℂ) (c : Fin r → ℂ) :
    ∑ l, (if (idx l).1 = σ then c (idx l).2 else 0) * F l = ∑ a, c a * F (idx.symm (σ, a)) := by
  rw [← idx.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    simp [hτ]
  · intro h; exact absurd (Finset.mem_univ σ) h

open NumberField Matrix in
open scoped nonZeroDivisors in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.per_move :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D
        : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm
        : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ
        : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+*
        ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx
        k).1.1 else (idx
        k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ
        ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
        (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
        ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ *
        _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ
        y))) → (∀ P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r → (D.La →+ (Fin g →
        ℂ)), (∀ x, (∀ v k, P x v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2)) → ∀ v, DifferentiableOn ℂ (fun x => P x v) (_root_.ReciprocityTheory.ChartRestriction.G.FD.GG
        Ψ Gm D.q)) ∧ (∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (γ : GL (Fin
        r) E) (P P' : D.La →+ (Fin g →
        ℂ)), (∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin
        r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ
        v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm u v) → (∀ v k, P v k = if ((idx
        k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → (∀ v k, P' v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → ∀ v v', φ v' = (γ : Matrix (Fin r) (Fin
        r) E) *ᵥ φ v → P' v' = P v) ∧ ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ Gm D.q, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r, ∀ (P
        P' : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → (∀ v k, P' v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ Gm D.q ∧ ∃ h : Matrix (Fin
        g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) ∧ (∀ k, h k k = if ((idx k).2 : ℕ) < D.q then b (idx
        k).1 (idx k).2 (idx k).2 else (b (idx k).1 (idx k).2 (idx
        k).2)⁻¹) ∧ h.det = ∏ k, h k k := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro P hP v
    rw [differentiableOn_pi]
    intro k
    simp only [hP]
    split_ifs
    · exact (differentiable_hermC_col_mat Gm _ _ _).differentiableOn
    · exact differentiableOn_mat_inv_mulVec_apply _ (fun x hx σ => (hx σ).1) _ _ _
  · intro x γ P P' hγ hP hP' v v' hv
    funext k
    rw [hP', hP, hv]
    have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1 =
        (γ : Matrix (Fin r) (Fin r) E).map (idx k).1.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1 := rfl
    rw [hmat, _root_.GlobalTheory.PerMove.emb_mulVec]
    split_ifs
    · rw [_root_.GlobalTheory.PerMove.col_mul, _root_.GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
    · have hunit : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map (idx k).1.1).det := by
        rw [show ((γ : Matrix (Fin r) (Fin r) E).map (idx k).1.1).det =
            (idx k).1.1 (γ : Matrix (Fin r) (Fin r) E).det from (RingHom.map_det _ _).symm]
        exact ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).map _
      rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
        Matrix.mul_one]
  · intro x hx b hb P P' hP hP'
    refine ⟨_root_.GlobalTheory.PerMove.rmul_mem_GG hx hb, ?_⟩
    classical
    let coeff : Fin g → Fin r → ℂ := fun k c =>
      if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1 c (idx k).2
      else (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1)⁻¹ (idx k).2 c
    let h : Matrix (Fin g) (Fin g) ℂ :=
      Matrix.of fun k l => if (idx l).1 = (idx k).1 then coeff k (idx l).2 else 0
    refine ⟨h, fun v => ?_, fun k => ?_, ?_⟩
    · funext k
      have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1 = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1 := rfl
      rw [hP', hmat, show (h *ᵥ P v) k = ∑ l, h k l * P v l from rfl]
      simp only [h, Matrix.of_apply]
      rw [sum_ite_fst_eq_sum_symm]
      simp only [hP, Equiv.apply_symm_apply, coeff]
      split_ifs with hk
      · rw [_root_.GlobalTheory.PerMove.hermC_col_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs with hc
        · rfl
        · rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1 c (idx k).2 = 0 from _root_.GlobalTheory.PerMove.bor_tri hb _ (by
            simp only [id_eq, Fin.lt_def]; omega), zero_mul, zero_mul]
      · rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs with hc
        · rw [show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b (idx k).1)⁻¹ (idx k).2 c = 0 from _root_.GlobalTheory.PerMove.bor_inv_tri hb _ (by
            simp only [id_eq, Fin.lt_def]; omega), zero_mul, zero_mul]
        · rfl
    · simp only [h, coeff, Matrix.of_apply, if_true]
      split_ifs
      · rfl
      · exact _root_.GlobalTheory.PerMove.bor_inv_diag hb _ _
    · let key : Fin r → ℤ := fun a => if (a : ℕ) < D.q then -(a : ℤ) else a
      let f : Fin g → ℕ ×ₗ ℤ := fun k => toLex ((Fintype.equivFin Ψ (idx k).1 : ℕ), key (idx k).2)
      have hkey : ∀ a c : Fin r, key a = key c → a = c := by
        intro a c hac
        simp only [key] at hac
        ext
        split_ifs at hac <;> omega
      refine _root_.GlobalTheory.PerMove.det_of_triangular f (fun k l hkl => ?_) h fun k l hlt => ?_
      · simp only [f, toLex_inj, Prod.mk.injEq] at hkl
        apply idx.injective
        exact Prod.ext ((Fintype.equivFin Ψ).injective (Fin.ext hkl.1)) (hkey _ _ hkl.2)
      · simp only [h, Matrix.of_apply]
        split_ifs with hσ
        · have hk : key (idx l).2 < key (idx k).2 := by
            rcases (Prod.Lex.toLex_lt_toLex).mp hlt with h1 | ⟨_, h2⟩
            · simp only [hσ] at h1
              exact absurd h1 (lt_irrefl _)
            · exact h2
          simp only [key] at hk
          simp only [coeff]
          split_ifs with ha
          · exact _root_.GlobalTheory.PerMove.bor_tri hb _ (by simp only [id_eq, Fin.lt_def]; split_ifs at hk <;> omega)
          · exact _root_.GlobalTheory.PerMove.bor_inv_tri hb _ (by simp only [id_eq, Fin.lt_def]; split_ifs at hk <;> omega)
        · rfl

end GlobalTheory

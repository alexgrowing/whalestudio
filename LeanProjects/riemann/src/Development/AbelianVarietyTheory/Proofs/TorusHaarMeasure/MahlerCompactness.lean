import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianLatticeMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralBasisReduction

namespace GlobalTheory.FlagMahler

open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

section
open Complex

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
open Complex in
theorem _root_.GlobalTheory.FlagMahler.col_map_eq (P : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (k : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (P.map τ) k = _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (P *ᵥ Pi.single k 1) := by
  ext a
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← one_mulVec u, ← one_mulVec w, ← h1]
  rw [hermC_expand, hermC_expand]
  simp only [hγ, one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ X.Gm (γ.map τ * Y) = gram τ X.Gm Y := by
  ext a b
  simp only [gram, of_apply]
  have hc : ∀ c, col (γ.map τ * Y) c = (γ.map τ) *ᵥ col Y c := by
    intro c; funext i; simp [col, Matrix.mul_apply, mulVec, dotProduct]
  rw [hc, hc, hermC_stab X hγ]

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
open Complex in
theorem _root_.GlobalTheory.FlagMahler.inv_lact (γ : GL (Fin r) E) (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ * Y)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v =
      Y⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  have h : ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ =
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ τ.map_zero τ.map_one]
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, h]
  congr 1
  ext i
  exact (RingHom.map_mulVec τ _ v i).symm

theorem entry_bound {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set Gt := X.Gm.map τ with hGtdef
  have hGt : Gt.det ≠ 0 := by
    have e : (X.Gm.map τ).det = τ X.Gm.det := by rw [RingHom.map_det]; rfl
    rw [hGtdef, e]; exact (map_ne_zero τ).mpr X.Gm_det
  have hGG : Gt * Gt⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGt)
  set q : Fin r → ℂ := fun k => conj (Gt⁻¹ k l) with hq
  have h1 : hermC τ X.Gm (col Y b) q = Y l b := by
    have e : ∀ a, ∑ c, Y a b * τ (X.Gm a c) * conj (q c) = Y a b * (Gt * Gt⁻¹) a l := by
      intro a
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hq, Complex.conj_conj, hGtdef, Matrix.map_apply]
      ring
    simp only [hermC, col]
    simp_rw [e, hGG, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have h2 := IntegralBasisReduction.hermC_normal X hY _ hg (col Y b) q
  have h3 : Y⁻¹ *ᵥ col Y b = Pi.single b 1 := by
    have : col Y b = Y *ᵥ Pi.single b 1 := by funext i; simp [col]
    rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hY), one_mulVec]
  rw [h3] at h2
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  rw [← h1, h2, norm_mul, Complex.norm_conj]
  have hs : ‖(((sgn X.p0 (b : ℕ) : ℝ) : ℂ))‖ = 1 := by
    unfold sgn; split_ifs <;> simp
  rw [hs, one_mul]
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, hq, Complex.norm_conj, mul_comm]

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
open Complex in
theorem _root_.GlobalTheory.FlagMahler.comp_le_Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ)
    (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) b‖ ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y p := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy
  calc X.c τ * ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) b‖ ^ 2
      ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun a => ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 p) a‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_univ b)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ).le
    _ ≤ ∑ σ, X.c σ * ∑ a, ‖((y σ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb σ.1 p) a‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun σ => X.c σ * ∑ a, ‖((y σ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb σ.1 p) a‖ ^ 2)
          (fun σ _ => mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X σ).le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
          (Finset.mem_univ τ)

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
open Complex in
theorem _root_.GlobalTheory.FlagMahler.comb_bound (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ)
    {ι : Type} [Fintype ι] (q : ι → ℚ) (f : ι → Fin r → E) (b : Fin r) :
    ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (∑ i, q i • f i)) b‖ ≤
      ∑ i, ‖(q i : ℂ)‖ * (1 + _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (f i) / X.c τ) := by
  have he : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (∑ i, q i • f i) = ∑ i, (q i : ℂ) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (f i) := by
    ext a
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Finset.sum_apply, map_sum, Rat.smul_def]
  rw [he, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ
  have h := _root_.GlobalTheory.FlagMahler.comp_le_Qy X y τ (f i) b
  have h2 : ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (f i)) b‖ ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (f i) / X.c τ := by
    rw [le_div_iff₀ hc]; linarith
  nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (f i)) b‖ - 1)]

def Kset (R : ℝ) : Set (Frame X.Ψ r) :=
  {w | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat w τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ a c, ‖w τ a c‖ ≤ R}

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.FlagMahler.Kset_compact (R : ℝ) :
    IsCompact (_root_.GlobalTheory.FlagMahler.Kset X R) := by
  change IsCompact (_root_.GlobalTheory.FlagMahler.Kset X R : Set (X.Ψ → Fin r → Fin r → ℂ))
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : (_root_.GlobalTheory.FlagMahler.Kset X R : Set (X.Ψ → Fin r → Fin r → ℂ)) = ⋂ τ : X.Ψ,
        ({w : X.Ψ → Fin r → Fin r → ℂ | _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (Matrix.of (w τ)) =
          diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ))} ∩
          ⋂ a : Fin r, ⋂ c : Fin r, {w | ‖w τ a c‖ ≤ R}) := by
      ext w
      simp only [_root_.GlobalTheory.FlagMahler.Kset, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Set.mem_setOf_eq, Set.mem_iInter,
        Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ ?_
    · refine isClosed_eq ?_ continuous_const
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply]
      fun_prop
    · exact isClosed_iInter fun a => isClosed_iInter fun c =>
        isClosed_le (by fun_prop) continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨|R|, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun c => ?_
    exact ((hw τ).2 a c).trans (le_abs_self R)

theorem det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : gram τ X.Gm Y *ᵥ star v = 0 := by
    funext a
    have e : ∑ b, hermC τ X.Gm (col Y a) (col Y b) * star (v b) = hermC τ X.Gm (col Y a) (Y *ᵥ v) := by
      rw [Data.mulVec_eq_sum_col, hermC_sum_right]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hermC_smul_right, Complex.star_def, mul_comm]
    simp only [mulVec, dotProduct, gram, of_apply, Pi.zero_apply, Pi.star_apply]
    rw [e, hv0, hermC_zero_right]
  rw [hg] at h1
  apply hv
  funext b
  have h2 := congrFun h1 b
  rw [mulVec_diagonal] at h2
  have hs : ((sgn p0 (b : ℕ) : ℝ) : ℂ) ≠ 0 := by unfold sgn; split_ifs <;> norm_num
  have h3 : star (v b) = 0 := (mul_eq_zero.mp h2).resolve_left hs
  simpa using h3

theorem Kset_sub (R : ℝ) : Kset X R ⊆ X.dom := by
  intro w hw τ
  have hg := (hw τ).1
  refine ⟨det_ne_of_gram X hg, fun i => ?_⟩
  have e : dmin X.Gm w τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hg, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
    simp only [psgn, Complex.ofReal_prod, Fin.val_castLE]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [e, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

end

theorem norm_herm_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) {C : ℝ}
    {p q : Fin r → E} (hp : QuadraticLatticeForms.Qy X y p ≤ C) (hq : QuadraticLatticeForms.Qy X y q ≤ C) (τ : X.Ψ) :
    ‖τ.1 (herm X.Gm p q)‖ ≤ r * (C / X.c τ) := by
  rw [← hermC_emb, IntegralBasisReduction.hermC_normal X (hy τ).1 _ (hy τ).2]
  refine (norm_sum_le _ _).trans ?_
  have hc := QuadraticLatticeForms.c_pos X τ
  calc _ ≤ ∑ _a : Fin r, C / X.c τ := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hs : ‖(((sgn X.p0 (a : ℕ) : ℝ) : ℂ))‖ = 1 := by
          unfold sgn; split_ifs <;> simp
        rw [norm_mul, norm_mul, hs, one_mul, Complex.norm_conj]
        have h1 := (comp_le_Qy X y τ p a).trans hp
        have h2 := (comp_le_Qy X y τ q a).trans hq
        rw [le_div_iff₀ hc]
        set u := ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖
        set w := ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 q) a‖
        nlinarith [mul_nonneg hc.le (sq_nonneg (u - w))]
    _ = _ := by simp

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FlagMahler.Qy_smul_le (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (α • v) ≤ (∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2) * _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have he : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (α • v) = (τ.1 α) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v := by
    ext a
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  rw [he, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum]
  have h1 : ‖τ.1 α‖ ^ 2 ≤ ∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2 :=
    Finset.single_le_sum (f := fun σ : X.Ψ => ‖σ.1 α‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ τ)
  have h2 : 0 ≤ ∑ a, ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) a‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 := (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ).le
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg h3 h2)]

theorem finite_bounded (B : X.Ψ → ℝ) :
    {α : E | IsIntegral ℤ ((X.den : E) * α) ∧ ∀ τ : X.Ψ, ‖τ.1 α‖ ≤ B τ}.Finite := by
  have hd : (X.den : E) ≠ 0 := by exact_mod_cast X.den_ne
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    (∑ τ : X.Ψ, ‖τ.1 (X.den : E)‖ * |B τ|)
  refine (hfin.preimage (f := fun α => (X.den : E) * α)
    (fun a _ b _ h => mul_left_cancel₀ hd h)).subset ?_
  rintro α ⟨h1, h2⟩
  have key : ∀ τ : X.Ψ, ‖τ.1 ((X.den : E) * α)‖ ≤ ∑ τ : X.Ψ, ‖τ.1 (X.den : E)‖ * |B τ| := by
    intro τ
    rw [map_mul, norm_mul]
    refine (mul_le_mul_of_nonneg_left ((h2 τ).trans (le_abs_self _)) (norm_nonneg _)).trans ?_
    exact Finset.single_le_sum (f := fun τ : X.Ψ => ‖τ.1 (X.den : E)‖ * |B τ|)
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  refine ⟨h1, fun φ => ?_⟩
  by_cases hφ : φ ∈ X.Ψ
  · exact key ⟨φ, hφ⟩
  · have h3 : ComplexEmbedding.conjugate φ ∈ X.Ψ :=
      (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact hφ)
    have h4 := key ⟨_, h3⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h4
    exact h4

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.FlagMahler.finite_int_sq (D : ℝ) : {n : ℤ | (n : ℝ) ^ 2 ≤ D}.Finite := by
  refine (Set.finite_Icc (-(⌈|D|⌉ + 1)) (⌈|D|⌉ + 1)).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn
  have hc : |D| ≤ (⌈|D|⌉ : ℝ) := Int.le_ceil _
  have hD := le_abs_self D
  have h1 : (n : ℝ) ≤ ⌈|D|⌉ + 1 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have h2 : -((⌈|D|⌉ : ℝ) + 1) ≤ n := by nlinarith [sq_nonneg ((n : ℝ) + 1)]
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩

theorem finite_types {ι : Type} [Fintype ι] [DecidableEq ι] (C D : ℝ) (hD : 0 ≤ D) :
    (HermitianLatticeMaps.ty X '' {f : Basis ι ℤ X.Λ | ∃ y, IntegralBasisReduction.IsNormal X y ∧
      (∀ i, QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
      ∀ (v : X.Λ) (i : ι), ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ D * QuadraticLatticeForms.Qy X y v}).Finite := by
  have h1 := finite_bounded X fun τ => r * (C / X.c τ)
  have h2 := fun k : Free.ChooseBasisIndex ℤ (𝓞 E) =>
    finite_int_sq (D * ((∑ σ : X.Ψ, ‖σ.1 (RingOfIntegers.basis E k : E)‖ ^ 2) * C))
  have h3 := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' fun _ : ι => h1)
  have h4 := Set.Finite.pi' (fun k => Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => h2 k)
  refine (h3.prod h4).subset ?_
  rintro _ ⟨f, ⟨y, hy, hf, hr⟩, rfl⟩
  refine ⟨fun i j => ⟨X.Λ_int _ (f i).2 _ (f j).2, norm_herm_le X hy (hf i) (hf j)⟩,
    fun k i j => ?_⟩
  refine (hr _ j).trans (mul_le_mul_of_nonneg_left ?_ hD)
  rw [HermitianLatticeMaps.smul_coe]
  exact (Qy_smul_le X y _ _).trans (mul_le_mul_of_nonneg_left (hf i)
    (Finset.sum_nonneg fun _ _ => by positivity))

noncomputable def bound {ι : Type} [Fintype ι] (C : ℝ) (g : Basis ι ℤ X.Λ) (s : GL (Fin r) E) : ℝ :=
  ∑ τ : X.Ψ, ∑ l : Fin r, ∑ k : Fin r, ‖(X.Gm.map τ.1)⁻¹ k l‖ *
    ∑ i, ‖(((RealPlaceEmbeddings.qb X g).repr ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i : ℚ) : ℂ)‖ *
      (1 + |C| / X.c τ)

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem finite_setOf_reduced_bounded_invariants (C m : ℝ) (hm : 0 < m) :
    {t | ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f = t ∧
      ∃ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.IsNormal X y ∧ (∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
        ∀ (v : X.Λ) i, ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ finrank ℤ X.Λ * _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v / m}.Finite := by
  classical
  have hΨ : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ hφ
    refine (X.cmType (ComplexEmbedding.conjugate φ)).mpr ?_
    simpa [ComplexEmbedding.conjugate] using hφ
  set B' : ℝ := ∑ τ : X.Ψ, r * |C| / X.c τ with hB'
  have hherm : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.IsNormal X y → ∀ u v : Fin r → E, _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y u ≤ C → _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v ≤ C →
      ∀ φ : E →+* ℂ, ‖φ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v)‖ ≤ B' := by
    intro y hy u v hu hv
    have key : ∀ τ : X.Ψ, ‖τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v)‖ ≤ B' := by
      intro τ
      have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ
      refine le_trans ?_ (Finset.single_le_sum (f := fun σ : X.Ψ => (r : ℝ) * |C| / X.c σ)
        (fun σ _ => by have := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X σ; positivity) (Finset.mem_univ τ))
      rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, _root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.hermC_normal X (hy τ).1 _ (hy τ).2]
      refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (?_ : _ ≤ |C| / X.c τ))).trans ?_
      · have hsn : ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
          unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
        rw [norm_mul, norm_mul, Complex.norm_conj, hsn, one_mul]
        have h1 := _root_.GlobalTheory.FlagMahler.comp_le_Qy X y τ u a
        have h2 := _root_.GlobalTheory.FlagMahler.comp_le_Qy X y τ v a
        rw [le_div_iff₀ hc]
        nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u) a‖ - ‖((y τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) a‖),
          le_abs_self C]
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]
    intro φ
    by_cases hφ : φ ∈ X.Ψ
    · exact key ⟨φ, hφ⟩
    · have := key ⟨_, hΨ φ hφ⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
  have hden : (X.den : E) ≠ 0 := by exact_mod_cast X.den_ne
  set Fz : Set E := {z | IsIntegral ℤ ((X.den : E) * z) ∧ ∀ φ : E →+* ℂ,
    ‖φ ((X.den : E) * z)‖ ≤ (∑ ψ : E →+* ℂ, ‖ψ (X.den : E)‖) * B'} with hFzdef
  have hFz : Fz.Finite :=
    ((Embeddings.finite_of_norm_le E ℂ ((∑ ψ : E →+* ℂ, ‖ψ (X.den : E)‖) * B')).preimage
      (fun a _ b _ h => mul_left_cancel₀ hden h)).subset fun z hz => hz
  refine ((Set.Finite.pi fun i => Set.Finite.pi fun j => hFz).prod
    (Set.Finite.pi fun k => Set.Finite.pi fun i => Set.Finite.pi fun j =>
      _root_.GlobalTheory.FlagMahler.finite_int_sq (9 ^ finrank ℤ X.Λ *
        ((∑ σ : X.Ψ, ‖σ.1 (RingOfIntegers.basis E k : E)‖ ^ 2) * |C|) / m))).subset ?_
  rintro t ⟨f, rfl, y, hy, hfC, hfrep⟩
  refine ⟨?_, ?_⟩
  · simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty, Set.mem_pi, Set.mem_univ, true_implies]
    intro i j
    refine ⟨X.Λ_int _ (f i).2 _ (f j).2, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun ψ : E →+* ℂ => ‖ψ (X.den : E)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)) (hherm y hy _ _ (hfC i) (hfC j) φ)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  · simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    intro k i j
    refine (hfrep _ j).trans ?_
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hm.le
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.smul_coe]
    exact (_root_.GlobalTheory.FlagMahler.Qy_smul_le X y _ _).trans (mul_le_mul_of_nonneg_left
      ((hfC i).trans (le_abs_self C)) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem gram_eq_transpose_mul_map (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G Y = Yᵀ * G.map τ * Y.map (starRingEnd ℂ) := by
  ext a b
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem kset_subset_dom (R : ℝ) :
    _root_.GlobalTheory.FlagMahler.Kset X R ⊆ X.dom := by
  intro w hw
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  intro τ
  have hg := (hw τ).1
  have hs : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := by
    intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
  refine ⟨?_, fun i => ?_⟩
  · intro h0
    have := congrArg Matrix.det hg
    rw [gram_eq_transpose_mul_map, det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul,
      det_diagonal] at this
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast hs a) this.symm
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
    rw [hg, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal, Finset.prod_range]
    simp only [Function.comp_apply, Fin.coe_castLE]
    rw [← Complex.ofReal_prod, Complex.ofReal_re, ← Finset.prod_mul_distrib]
    exact Finset.prod_pos fun a _ => mul_self_pos.mpr (hs _)

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem gram_map_mul_of_isUStab {γ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ)
    (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ * Y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm Y := by
  have hG : (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc =
      X.Gm := by
    ext a b
    have := hγ.1 (Pi.single a 1) (Pi.single b 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm at this
    simp [mulVec_single, Pi.single_apply, apply_ite _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_one, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_zero] at this
    rw [← this]
    simp only [Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc).map τ := by
    ext a b
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc]
  rw [gram_eq_transpose_mul_map, gram_eq_transpose_mul_map, Matrix.map_mul, hc, transpose_mul]
  calc Yᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * X.Gm.map τ *
        (((γ : Matrix (Fin r) (Fin r) E).map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc).map τ * Y.map (starRingEnd ℂ))
      = Yᵀ * (((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm *
          (γ : Matrix (Fin r) (Fin r) E).map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc).map τ) * Y.map (starRingEnd ℂ) := by
        rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hG]

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem norm_entry_le_of_gram_eq_diagonal_sgn (τ : X.Ψ) (W : Matrix (Fin r) (Fin r) ℂ)
    (hW : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm W = diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ)))
    (l c : Fin r) :
    ‖W l c‖ ≤ ∑ k, ‖(X.Gm.map τ.1)⁻¹ k l‖ * ‖(W⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (Pi.single k 1)) c‖ := by
  have hG : IsUnit (X.Gm.map τ.1).det := by
    rw [show (X.Gm.map τ.1).det = τ.1 X.Gm.det from (RingHom.map_det τ.1 X.Gm).symm]
    exact ((map_ne_zero τ.1).mpr X.Gm_det).isUnit
  have hs : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := by
    intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
  have hWd : IsUnit W.det := by
    refine (Ne.isUnit fun h0 => ?_)
    have := congrArg Matrix.det hW
    rw [gram_eq_transpose_mul_map, det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul,
      det_diagonal] at this
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast hs a) this.symm
  have hM : (Wᴴ * (X.Gm.map τ.1)ᵀ) * W =
      diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ)) := by
    have := congrArg transpose hW
    rw [gram_eq_transpose_mul_map, transpose_mul, transpose_mul, transpose_transpose,
      diagonal_transpose] at this
    rw [Matrix.mul_assoc]
    exact this
  have hMu : IsUnit (Wᴴ * (X.Gm.map τ.1)ᵀ).det := by
    rw [det_mul, det_conjTranspose, det_transpose]
    exact hWd.star.mul hG
  have hWeq : W l c = (((X.Gm.map τ.1)⁻¹)ᵀ * (W⁻¹)ᴴ *
      diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ))) l c := by
    have h1 : W = (Wᴴ * (X.Gm.map τ.1)ᵀ)⁻¹ *
        diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ)) := by
      rw [← hM, Matrix.nonsing_inv_mul_cancel_left _ _ hMu]
    nth_rewrite 1 [h1]
    simp only [Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv, Matrix.conjTranspose_nonsing_inv]
  have hr : ∀ k, (W⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (Pi.single k 1)) c = W⁻¹ c k := by
    intro k
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (Pi.single k (1 : E)) = Pi.single k 1 := by
      ext a
      simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.single_apply, apply_ite τ.1]
    rw [this]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [hr]
  have hsn : ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1 := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
  rw [hWeq, mul_diagonal, Matrix.mul_apply, norm_mul, hsn, mul_one]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, transpose_apply, conjTranspose_apply, norm_star]

open NumberField Module in
open Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FlagMahler.mahler_compactness : _root_.ReciprocityTheory.ChartRestriction.G.FD.MahlerCompactnessCriterion (E := E) := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.MahlerCompactnessCriterion
  intro r X ε hε
  obtain ⟨S, hS⟩ := X.Γ_index
  set n := finrank ℤ X.Λ with hn
  have hm : 0 < ε ^ 2 := by positivity
  set C : ℝ := 2 ^ (n * (n - 1)) * |(_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Bm X (_root_.ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (n - 1) with hC
  set T := {t | ∃ f : Basis (Fin n) ℤ X.Λ, _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f = t ∧
      ∃ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.IsNormal X y ∧ (∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
        ∀ (v : X.Λ) i, ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ n * _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v / ε ^ 2} with hTdef
  have hT : T.Finite := finite_setOf_reduced_bounded_invariants X C (ε ^ 2) hm
  let g : _ → Basis (Fin n) ℤ X.Λ := fun t => if h : t ∈ T then Classical.choose h else _root_.ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb X
  have hg : ∀ t ∈ T, _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X (g t) = t := by
    intro t ht
    simp only [g, dif_pos ht]
    exact (Classical.choose_spec ht).1
  set R : ℝ := ∑ t ∈ hT.toFinset, ∑ s ∈ S, |_root_.GlobalTheory.FlagMahler.bound X C (g t) s| with hR
  refine ⟨_root_.GlobalTheory.FlagMahler.Kset X R, _root_.GlobalTheory.FlagMahler.Kset_compact X R,
    kset_subset_dom X R, ?_⟩
  intro x hx hla
  obtain ⟨b, hb, hnorm⟩ := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame X hx
  set y : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ with hy
  have hxdom := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hxdom
  have hbor := hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hbor
  have hynorm : _root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.IsNormal X y := by
    intro τ
    refine ⟨?_, (hnorm τ).1⟩
    show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hxdom τ).1 (hbor τ).1
  have hQy : ∀ v : Fin r → E,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v = ∑ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := by
    intro v
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [(hnorm τ).2]
  have hsq : ε ^ 2 ≤ X.firstMinimumSq x := by
    have h1 : ε ≤ √(X.firstMinimumSq x) := hla
    exact (Real.le_sqrt' hε).mp h1
  have hmin : ∀ v ∈ X.Λ, v ≠ 0 → ε ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X y v := by
    intro v hv hv0
    refine hsq.trans ?_
    rw [hQy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    refine csInf_le ⟨0, ?_⟩ ⟨v, hv, hv0, rfl⟩
    rintro t ⟨w, -, hw0, rfl⟩
    exact Finset.sum_nonneg fun τ _ =>
      mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ).le (X.maj_pos hx τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero τ.1 hw0)).le
  obtain ⟨f, hfC, hfrep⟩ := _root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.reduce X hynorm hm hmin
  have htT : _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f ∈ T := ⟨f, rfl, y, hynorm, hfC, hfrep⟩
  obtain ⟨γ, hγU, -, hγinv⟩ := _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.exists_gl X (f := f) (f' := g (_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f)) (hg _ htT).symm
  obtain ⟨s, hsS, hsΓ⟩ := hS γ hγU
  refine ⟨s⁻¹ * γ, hsΓ, b, hb, ?_⟩
  intro τ
  have hW : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact (s⁻¹ * γ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ =
      ((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * y τ := rfl
  have hgram : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact (s⁻¹ * γ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ) =
      diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ)) := by
    rw [hW, gram_map_mul_of_isUStab X (X.Γ_stab _ hsΓ)]
    exact (hnorm τ).1
  refine ⟨hgram, fun l c => ?_⟩
  have hcoord : ∀ k, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact (s⁻¹ * γ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ)⁻¹ *ᵥ
      _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (Pi.single k 1)) c‖ ≤
      ∑ i, ‖(((_root_.ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.qb X (g (_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f))).repr
        ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i : ℚ) : ℂ)‖ * (1 + |C| / X.c τ) := by
    intro k
    rw [hW, _root_.GlobalTheory.FlagMahler.inv_lact, _root_.mul_inv_rev, inv_inv, Units.val_mul,
      ← Matrix.mulVec_mulVec, hγinv]
    refine (_root_.GlobalTheory.FlagMahler.comb_bound X y τ _ (fun i => (f i : Fin r → E)) c).trans ?_
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X τ
    gcongr
    exact (hfC i).trans (le_abs_self C)
  have hentry := norm_entry_le_of_gram_eq_diagonal_sgn X τ _ hgram l c
  show ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact (s⁻¹ * γ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) τ l c‖ ≤ R
  refine hentry.trans ?_
  have hQ : ∀ (σ : X.Ψ) (k : Fin r), 0 ≤ ∑ i, ‖(((_root_.ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.qb X (g (_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f))).repr
      ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i : ℚ) : ℂ)‖ * (1 + |C| / X.c σ) :=
    fun σ k => Finset.sum_nonneg fun i _ =>
      mul_nonneg (norm_nonneg _) (by have := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.c_pos X σ; positivity)
  refine (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hcoord k) (norm_nonneg _)).trans ?_
  refine le_trans ?_ (le_trans (le_abs_self (_root_.GlobalTheory.FlagMahler.bound X C (g (_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f)) s)) ?_)
  · unfold _root_.GlobalTheory.FlagMahler.bound
    refine le_trans ?_ (Finset.single_le_sum (fun σ _ => Finset.sum_nonneg fun l' _ =>
      Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hQ σ k)) (Finset.mem_univ τ))
    exact Finset.single_le_sum (f := fun l' : Fin r => ∑ k : Fin r, ‖(X.Gm.map τ.1)⁻¹ k l'‖ *
      ∑ i, ‖(((_root_.ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.qb X (g (_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f))).repr
        ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i : ℚ) : ℂ)‖ * (1 + |C| / X.c τ))
      (fun l' _ => Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hQ τ k))
      (Finset.mem_univ l)
  · rw [hR]
    have ht : _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f ∈ hT.toFinset := hT.mem_toFinset.mpr htT
    refine le_trans ?_ (Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun s' _ =>
      abs_nonneg (_root_.GlobalTheory.FlagMahler.bound X C (g t) s')) ht)
    exact Finset.single_le_sum
      (f := fun s' => |_root_.GlobalTheory.FlagMahler.bound X C (g (_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.ty X f)) s'|)
      (fun _ _ => abs_nonneg _) hsS

end GlobalTheory.FlagMahler

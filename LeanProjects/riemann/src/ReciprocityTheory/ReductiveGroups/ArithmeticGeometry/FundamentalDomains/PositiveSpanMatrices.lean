import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnitaryComplementMoveOfIsotropic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def kap {n p : ℕ} (hp : p ≤ n) (a : Fin (n - p)) : Fin n := ⟨p + a, by have := a.isLt; omega⟩

def ext0 {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → M) (i : ℕ) : M :=
  if h : i < n then F ⟨i, h⟩ else 0

lemma sum_split {M : Type*} [AddCommMonoid M] {n p : ℕ} (hp : p ≤ n) (F : Fin n → M) :
    ∑ c : Fin n, F c = ∑ b : Fin p, F (Fin.castLE hp b) + ∑ a : Fin (n - p), F (kap hp a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hm : p + m - p = m := by omega
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl (fun b _ => congrArg F (Fin.ext rfl))) ?_
  refine Fintype.sum_equiv (finCongr hm.symm) _ _ (fun i => ?_)
  exact congrArg F (Fin.ext (by simp [kap]))

lemma kap_ne_castLE {n p : ℕ} (hp : p ≤ n) (a : Fin (n - p)) (b : Fin p) : kap hp a ≠ Fin.castLE hp b := by
  intro h
  have h1 := congrArg Fin.val h
  have hb := b.isLt
  simp [kap] at h1
  omega

lemma fin_cases_split {n p : ℕ} (hp : p ≤ n) (c : Fin n) :
    (∃ b : Fin p, c = Fin.castLE hp b) ∨ ∃ a : Fin (n - p), c = kap hp a := by
  have hc := c.isLt
  by_cases h : (c : ℕ) < p
  · exact Or.inl ⟨⟨c, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨c - p, by omega⟩, Fin.ext ?_⟩
    show (c : ℕ) = p + (c - p)
    omega

lemma span_eq_of_mat {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (f g : Fin n → V)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) (h : ∀ b, g b = ∑ b', A b' b • f b') :
    Submodule.span ℂ (Set.range g) = Submodule.span ℂ (Set.range f) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [h b]
    exact Submodule.sum_mem _ (fun b' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b', rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨b'', rfl⟩
    have hone : ∀ b', ∑ b, A⁻¹ b b'' * A b' b = (1 : Matrix (Fin n) (Fin n) ℂ) b' b'' := by
      intro b'
      rw [← Matrix.mul_nonsing_inv A hu, Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    have key : f b'' = ∑ b, A⁻¹ b b'' • g b := by
      simp_rw [h, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hone, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [key]
    exact Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))

lemma sgn_mul_self (p0 a : ℕ) : ((sgn p0 a : ℝ) : ℂ) * ((sgn p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> norm_num

section Ortho

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

abbrev Spos (x : Frame X.Ψ r) (τ : X.Ψ) : Submodule ℂ (Fin r → ℂ) :=
  Submodule.span ℂ (Set.range fun b : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le b))

def Pos (x : Frame X.Ψ r) (τ : X.Ψ) (y : Fin r → ℂ) : ℝ :=
  ∑ b : Fin X.p0, ‖hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b))‖ ^ 2

def Neg (x : Frame X.Ψ r) (τ : X.Ψ) (y : Fin r → ℂ) : ℝ :=
  ∑ a : Fin (r - X.p0), ‖hermC τ.1 X.Gm y (col (mat x τ) (kap X.p0_le a))‖ ^ 2

lemma Pos_nonneg (x : Frame X.Ψ r) (τ : X.Ψ) (y : Fin r → ℂ) : 0 ≤ Pos X x τ y := by
  unfold Pos
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma Neg_nonneg (x : Frame X.Ψ r) (τ : X.Ψ) (y : Fin r → ℂ) : 0 ≤ Neg X x τ y := by
  unfold Neg
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma ortho_apply {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (c d : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) c) (col (mat x τ) d) = if c = d then ((sgn X.p0 c : ℝ) : ℂ) else 0 := by
  have h := congrFun (congrFun (hx τ) c) d
  simpa [gram, Matrix.diagonal_apply] using h

lemma expand {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (y : Fin r → ℂ) :
    y = ∑ c : Fin r, (((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * hermC τ.1 X.Gm y (col (mat x τ) c)) • col (mat x τ) c := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨t, ht⟩ : ∃ t : Fin r → ℂ, y = ∑ c, t c • col (mat x τ) c := by
    refine ⟨(mat x τ)⁻¹ *ᵥ y, ?_⟩
    have h1 : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  have hc : ∀ c, hermC τ.1 X.Gm y (col (mat x τ) c) = t c * ((sgn X.p0 c : ℝ) : ℂ) := by
    intro c
    rw [ht, hermC_sum_left]
    simp_rw [hermC_smul_left, ortho_apply X hx τ]
    simp
  conv_lhs => rw [ht]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hc c, mul_comm (t c), ← mul_assoc, sgn_mul_self, one_mul]

lemma re_self {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (y : Fin r → ℂ) :
    (hermC τ.1 X.Gm y y).re = ∑ c : Fin r, sgn X.p0 (c : ℕ) * ‖hermC τ.1 X.Gm y (col (mat x τ) c)‖ ^ 2 := by
  have hs : ∀ c : Fin r, sgn X.p0 c * sgn X.p0 c = 1 := by
    intro c
    unfold sgn
    split_ifs <;> norm_num
  conv_lhs => rw [expand X hx τ hdet y]
  rw [hermC_quad]
  simp_rw [ortho_apply X hx τ]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_mul, Complex.conj_ofReal]
  have e : ((sgn X.p0 c : ℝ) : ℂ) * hermC τ.1 X.Gm y (col (mat x τ) c) * ((sgn X.p0 c : ℝ) : ℂ) *
      (((sgn X.p0 c : ℝ) : ℂ) * conj (hermC τ.1 X.Gm y (col (mat x τ) c))) =
      ((sgn X.p0 c * sgn X.p0 c * sgn X.p0 c * Complex.normSq (hermC τ.1 X.Gm y (col (mat x τ) c)) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj]
    ring
  rw [e, Complex.ofReal_re, hs, one_mul, Complex.normSq_eq_norm_sq]

lemma sgn_castLE (b : Fin X.p0) : sgn X.p0 (Fin.castLE X.p0_le b : ℕ) = 1 := by
  unfold sgn
  rw [if_pos (by simp [b.isLt])]

lemma sgn_kap (a : Fin (r - X.p0)) : sgn X.p0 (kap X.p0_le a : ℕ) = -1 := by
  unfold sgn
  rw [if_neg (by show ¬ (X.p0 + (a : ℕ) < X.p0); omega)]

lemma re_self_split {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (y : Fin r → ℂ) : (hermC τ.1 X.Gm y y).re = Pos X x τ y - Neg X x τ y := by
  rw [re_self X hx τ hdet y, sum_split X.p0_le]
  simp only [sgn_castLE X, sgn_kap X, one_mul, neg_one_mul, Finset.sum_neg_distrib]
  unfold Pos Neg
  ring

lemma eq_zero_of_Pos_Neg {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (y : Fin r → ℂ) (hP : Pos X x τ y = 0) (hN : Neg X x τ y = 0) : y = 0 := by
  unfold Pos at hP
  unfold Neg at hN
  have hP' : ∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
    intro b
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      sq_nonneg ‖hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le i))‖)).mp hP b (Finset.mem_univ _)
    simpa using h1
  have hN' : ∀ a : Fin (r - X.p0), hermC τ.1 X.Gm y (col (mat x τ) (kap X.p0_le a)) = 0 := by
    intro a
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      sq_nonneg ‖hermC τ.1 X.Gm y (col (mat x τ) (kap X.p0_le i))‖)).mp hN a (Finset.mem_univ _)
    simpa using h1
  have hall : ∀ c, hermC τ.1 X.Gm y (col (mat x τ) c) = 0 := by
    intro c
    rcases fin_cases_split X.p0_le c with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · exact hP' b
    · exact hN' a
  rw [expand X hx τ hdet y]
  simp [hall]

lemma perp_kap {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (w : Fin r → ℂ) (hw : w ∈ Spos X x τ)
    (a : Fin (r - X.p0)) : hermC τ.1 X.Gm w (col (mat x τ) (kap X.p0_le a)) = 0 := by
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    rw [ortho_apply X hx τ, if_neg (kap_ne_castLE X.p0_le a b).symm]
  | zero => exact hermC_zero_left _ _ _
  | add z1 z2 _ _ h1 h2 => rw [hermC_add_left, h1, h2, add_zero]
  | smul c z _ h => rw [hermC_smul_left, h, mul_zero]

lemma re_self_of_mem {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (w : Fin r → ℂ) (hw : w ∈ Spos X x τ) : (hermC τ.1 X.Gm w w).re = Pos X x τ w := by
  rw [re_self_split X hx τ hdet w]
  have hN : Neg X x τ w = 0 := by
    unfold Neg
    exact Finset.sum_eq_zero (fun a _ => by rw [perp_kap X hx τ w hw a]; simp)
  rw [hN, sub_zero]

lemma re_self_of_perp {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (w : Fin r → ℂ) (hw : ∀ b : Fin X.p0, hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) :
    (hermC τ.1 X.Gm w w).re = -Neg X x τ w := by
  rw [re_self_split X hx τ hdet w]
  have hP : Pos X x τ w = 0 := by
    unfold Pos
    exact Finset.sum_eq_zero (fun b _ => by rw [hw b]; simp)
  rw [hP, zero_sub]

lemma zero_of_mem_self {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (w : Fin r → ℂ) (hw : w ∈ Spos X x τ) (h0 : hermC τ.1 X.Gm w w = 0) : w = 0 := by
  have hre := re_self_of_mem X hx τ hdet w hw
  rw [h0, Complex.zero_re] at hre
  have hN : Neg X x τ w = 0 := by
    unfold Neg
    exact Finset.sum_eq_zero (fun a _ => by rw [perp_kap X hx τ w hw a]; simp)
  exact eq_zero_of_Pos_Neg X hx τ hdet w hre.symm hN

lemma ppos_mem (x : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) : X.ppos x τ w ∈ Spos X x τ := by
  unfold Data.ppos
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

lemma ppos_of_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) (hw : w ∈ Spos X x τ) :
    X.ppos x τ w = w := by
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  have hu : IsUnit (X.gramPos x τ).det := by
    open scoped ComplexOrder in
    exact (Matrix.isUnit_iff_isUnit_det _).mp (X.gramPos_posDef hx τ).isUnit
  have hin : ∀ b, hermC τ.1 X.Gm (∑ a, t a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = ∑ a, t a * X.gramPos x τ a b := by
    intro b
    rw [hermC_sum_left]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hermC_smul_left, X.gramPos_apply]
    rfl
  unfold Data.ppos
  simp_rw [hin]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have e : ∑ b, (∑ a', t a' * X.gramPos x τ a' b) * (X.gramPos x τ)⁻¹ b a =
      Matrix.vecMul (Matrix.vecMul t (X.gramPos x τ)) (X.gramPos x τ)⁻¹ a := rfl
  rw [e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]

lemma perp_of_ppos_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ)
    (hw : X.ppos x τ w = 0) (b : Fin X.p0) : hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  have hu : IsUnit (X.gramPos x τ).det := by
    open scoped ComplexOrder in
    exact (Matrix.isUnit_iff_isUnit_det _).mp (X.gramPos_posDef hx τ).isUnit
  have h1 : hermC τ.1 X.Gm (X.ppos x τ w) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
    rw [hw, hermC_zero_left]
  unfold Data.ppos at h1
  rw [hermC_sum_left] at h1
  simp_rw [hermC_smul_left] at h1
  have e2 : ∀ a, hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (col (mat x τ) (Fin.castLE X.p0_le b)) =
      X.gramPos x τ a b := fun a => (X.gramPos_apply x τ a b).symm
  simp_rw [e2] at h1
  have e : ∑ a, (∑ b', hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a) *
      X.gramPos x τ a b =
      Matrix.vecMul (Matrix.vecMul (fun b' => hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b')))
        (X.gramPos x τ)⁻¹) (X.gramPos x τ) b := rfl
  rw [e, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one] at h1
  exact h1

end Ortho

end

end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices

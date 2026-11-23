import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

namespace ReciprocityTheory.ChartRestriction.G.FD

open Matrix NumberField
open scoped ComplexOrder ComplexConjugate

theorem posDef_of_posSemidef_det {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (hd : A.det ≠ 0) : A.PosDef := by
  exact (Matrix.PosSemidef.posDef_iff_det_ne_zero hA).2 hd

theorem lminor_submatrix_castSucc {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    lminor (A.submatrix Fin.castSucc Fin.castSucc) i = lminor A i.castSucc := by
  unfold lminor
  rw [Matrix.submatrix_submatrix]
  rfl

theorem lminor_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : lminor A (Fin.last n) = A.det := by
  rfl

theorem posDef_of_lminor : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.IsHermitian →
    (∀ i : Fin (n + 1), 0 < (lminor A i).re) → A.PosDef
  | 0, A, hA, _ => ⟨hA, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  | n + 1, A, hA, hm => by
    set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'def
    have hA'h : A'.IsHermitian := hA.submatrix _
    have hA' : A'.PosDef := posDef_of_lminor n A' hA'h (fun i => by
      rw [lminor_submatrix_castSucc]; exact hm _)
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    set B := (A.submatrix e e).toBlocks₁₂ with hB
    set D := (A.submatrix e e).toBlocks₂₂ with hD
    have h11 : (A.submatrix e e).toBlocks₁₁ = A' := by
      ext i j; simp [Matrix.toBlocks₁₁, A', e]; rfl
    have h21 : (A.submatrix e e).toBlocks₂₁ = Bᴴ := by
      ext i j
      simp only [hB, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.submatrix_apply]
      exact (hA.apply _ _).symm
    have hblk : A.submatrix e e = fromBlocks A' B Bᴴ D := by
      rw [← h11, ← h21]; exact (fromBlocks_toBlocks _).symm
    let _ : Invertible A' := hA'.isUnit.invertible
    set S := D - Bᴴ * A'⁻¹ * B with hS
    have hdet : A.det = A'.det * S.det := by
      rw [← det_submatrix_equiv_self e A, hblk, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    have hreal : ∀ {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}, M.IsHermitian → (M.det.im = 0) := by
      intro M hM
      have h := congrArg Matrix.det hM
      rw [det_conjTranspose] at h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hAd : A.det = ((A.det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal hA])
    have hApos : 0 < A.det.re := by rw [← lminor_last]; exact hm _
    have hA'pos : 0 < A'.det := hA'.det_pos
    have hS00 : S.det = A.det / A'.det := by
      rw [hdet]; field_simp [hA'pos.ne']
    have hSpos : 0 < S.det := by
      rw [hS00, hAd]
      exact div_pos (by exact_mod_cast hApos) hA'pos
    have hSdet : S.det = S 0 0 := Matrix.det_unique S
    have hSh : S.IsHermitian := by
      ext i j
      rw [show i = 0 from Subsingleton.elim _ _, show j = 0 from Subsingleton.elim _ _]
      simp only [Matrix.conjTranspose_apply]
      rw [← hSdet, Complex.star_def, Complex.conj_eq_iff_im]
      exact (Complex.pos_iff.mp hSpos).2.symm
    have hSpsd : S.PosSemidef := by
      rw [posSemidef_iff_dotProduct_mulVec]
      refine ⟨hSh, fun x => ?_⟩
      simp only [dotProduct, mulVec, Fin.sum_univ_one, Pi.star_apply]
      have : star (x 0) * (S 0 0 * x 0) = S 0 0 * (star (x 0) * x 0) := by ring
      rw [this, ← hSdet]
      exact mul_nonneg hSpos.le (star_mul_self_nonneg _)
    have hMpsd : (A.submatrix e e).PosSemidef := by
      rw [hblk]; exact (PosDef.fromBlocks₁₁ B D hA').mpr hSpsd
    have hApsd : A.PosSemidef := (posSemidef_submatrix_equiv e).mp hMpsd
    exact posDef_of_posSemidef_det hApsd (fun h => by simp [h] at hApos)

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_add_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermC_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (c • u) v = c * hermC τ G u v := by
  unfold hermC
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hermC_sub_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  unfold hermC
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem hermC_zero_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) :
    hermC τ G 0 v = 0 := by
  unfold hermC
  simp

theorem hermC_add_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hermC_smul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  unfold hermC
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hermC_sub_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  unfold hermC
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem hermC_zero_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ) :
    hermC τ G u 0 = 0 := by
  unfold hermC
  simp

theorem hermC_sum_left {ι : Type} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ G (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hermC_zero_left τ G v
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_left, ih]

theorem hermC_sum_right {ι : Type} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) :
    hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hermC_zero_right τ G u
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hermC_add_right, ih]

theorem hermC_conj (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (u v : Fin r → ℂ) : conj (hermC τ G u v) = hermC τ G v u := by
  unfold hermC
  simp only [map_sum, map_mul, Complex.conj_conj]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← emb_cc, hG]
  ring

theorem gram_isHermitian (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (M : Matrix (Fin r) (Fin r) ℂ) : (gram τ G M).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [gram, Matrix.of_apply]
  exact hermC_conj τ hG _ _

end Herm

section Quad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem quad_re_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {c : Fin n → ℂ}
    (hc : c ≠ 0) : 0 < (∑ a, ∑ b, c a * M a b * conj (c b)).re := by
  have hc' : star c ≠ 0 := fun h0 => hc (by simpa using congrArg star h0)
  have h := hM.dotProduct_mulVec_pos hc'
  have e : star (star c) ⬝ᵥ (M *ᵥ star c) = ∑ a, ∑ b, c a * M a b * conj (c b) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e] at h
  have h' := (Complex.lt_def.1 h).1
  rwa [Complex.zero_re] at h'

theorem quad_re_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (c : Fin n → ℂ) :
    0 ≤ (∑ a, ∑ b, c a * M a b * conj (c b)).re := by
  have h : 0 ≤ star (star c) ⬝ᵥ (M *ᵥ star c) := hM.dotProduct_mulVec_nonneg (star c)
  have e : star (star c) ⬝ᵥ (M *ᵥ star c) = ∑ a, ∑ b, c a * M a b * conj (c b) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e] at h
  have h' := (Complex.le_def.1 h).1
  rwa [Complex.zero_re] at h'

theorem hermC_quad (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (γ : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ a, γ a • f a) (∑ b, γ b • f b) =
      ∑ a, ∑ b, γ a * hermC τ G (f a) (f b) * conj (γ b) := by
  rw [hermC_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_smul_right]
  ring

end Quad

theorem psgn_eq_one {p0 i : ℕ} (h : i ≤ p0) : psgn p0 i = 1 := by
  unfold psgn
  refine Finset.prod_eq_one fun a ha => ?_
  have hlt : a < p0 := lt_of_lt_of_le (Finset.mem_range.1 ha) h
  unfold sgn
  rw [if_pos hlt]

namespace Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def colP (x : Frame X.Ψ r) (τ : X.Ψ) (a : Fin X.p0) : Fin r → ℂ :=
  col (mat x τ) (Fin.castLE X.p0_le a)

theorem gramPos_apply (x : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin X.p0) :
    X.gramPos x τ a b = hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) := rfl

theorem gramPos_isHermitian (x : Frame X.Ψ r) (τ : X.Ψ) : (X.gramPos x τ).IsHermitian := by
  exact (gram_isHermitian τ.1 X.Gm_herm (mat x τ)).submatrix (Fin.castLE X.p0_le)

theorem mem_dom_iff (x : Frame X.Ψ r) : x ∈ X.dom ↔
    ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := Iff.rfl

theorem gramPos_posDef {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).PosDef := by
  have hx' := ((X.mem_dom_iff x).1 hx τ).2
  refine posDef_of_lminor X.p0 _ (X.gramPos_isHermitian x τ) fun i => ?_
  have h1 := hx' (Fin.castLE (Nat.succ_le_succ X.p0_le) i)
  have h2 : psgn X.p0 ((Fin.castLE (Nat.succ_le_succ X.p0_le) i : Fin (r + 1)) : ℕ) = 1 :=
    psgn_eq_one (Nat.le_of_lt_succ i.isLt)
  rw [h2, one_mul] at h1
  exact h1

theorem ppos_eq (x : Frame X.Ψ r) (τ : X.Ψ) (u : Fin r → ℂ) : X.ppos x τ u =
    ∑ a, (∑ b, hermC τ.1 X.Gm u (X.colP x τ b) * (X.gramPos x τ)⁻¹ b a) • X.colP x τ a := rfl

private theorem isUnit_det_of_posDef_fundamental_domains {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (h : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.2 ((Matrix.PosSemidef.posDef_iff_det_ne_zero h.posSemidef).1 h)

theorem hermC_ppos_colP {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u : Fin r → ℂ) (d : Fin X.p0) :
    hermC τ.1 X.Gm (X.ppos x τ u) (X.colP x τ d) = hermC τ.1 X.Gm u (X.colP x τ d) := by
  have hA : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef_fundamental_domains (X.gramPos_posDef hx τ))
  rw [X.ppos_eq x τ u, hermC_sum_left]
  simp_rw [hermC_smul_left, ← X.gramPos_apply x τ, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Matrix.mul_apply, hA, Matrix.one_apply]
  simp

theorem hermC_ppos_self (τ : X.Ψ) (x : Frame X.Ψ r) (u : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) u = ∑ a, ∑ b, hermC τ.1 X.Gm u (X.colP x τ a) *
      (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm u (X.colP x τ b)) := by
  rw [X.ppos_eq x τ u, hermC_sum_left]
  simp_rw [hermC_smul_left, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hermC_conj τ.1 X.Gm_herm u (X.colP x τ j)]

theorem Hf_eq_two_ppos (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = 2 * hermC τ.1 X.Gm (X.ppos x τ u) w - hermC τ.1 X.Gm u w := by
  show hermC τ.1 X.Gm ((2 : ℂ) • X.ppos x τ u - u) w = _
  rw [hermC_sub_left, hermC_smul_left]

theorem mulVec_eq_sum_col (P : Matrix (Fin r) (Fin r) ℂ) (c : Fin r → ℂ) :
    P *ᵥ c = ∑ i, c i • col P i := by
  ext k
  simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]

private theorem hermC_sum_smul_col_negative_block {p0 : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ)
    (hP : gram τ G P = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (n' : Fin (r - p0) → Fin r) (hn' : ∀ j, (n' j : ℕ) = p0 + (j : ℕ)) (β : Fin (r - p0) → ℂ) :
    hermC τ G (∑ j, β j • col P (n' j)) (∑ j, β j • col P (n' j)) =
      -∑ j, β j * conj (β j) := by
  rw [hermC_quad]
  have hcol : ∀ j k, hermC τ G (col P (n' j)) (col P (n' k)) = if j = k then -1 else 0 := by
    intro j k
    have h1 : hermC τ G (col P (n' j)) (col P (n' k)) = gram τ G P (n' j) (n' k) := rfl
    rw [h1, hP, Matrix.diagonal_apply]
    by_cases hjk : j = k
    · subst hjk
      have hlt : ¬ ((n' j : ℕ) < p0) := by rw [hn']; omega
      simp [sgn, hlt]
    · have hne : n' j ≠ n' k := fun h => hjk (Fin.ext (by
        have h2 := congrArg Fin.val h
        rw [hn', hn'] at h2
        omega))
      simp [hne, hjk]
  simp_rw [hcol]
  simp

theorem neg_of_perp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {e : Fin r → ℂ} (he : e ≠ 0)
    (hperp : ∀ b, hermC τ.1 X.Gm e (X.colP x τ b) = 0) : (hermC τ.1 X.Gm e e).re < 0 := by
  classical
  by_contra hneg
  push_neg at hneg
  obtain ⟨P, -, hP⟩ := X.signature τ
  have hpd := X.gramPos_posDef hx τ
  have hle := X.p0_le
  let n' : Fin (r - X.p0) → Fin r := fun j => ⟨X.p0 + j, by have := j.isLt; omega⟩
  have hnli : ¬ LinearIndependent ℂ (Sum.elim (fun o : Option (Fin X.p0) => o.elim e (X.colP x τ))
      (fun j : Fin (r - X.p0) => col P (n' j))) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin,
      Module.finrank_fin_fun] at h1
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hnli
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim] at hg
  set α0 := g (Sum.inl none) with hα0def
  set vW := ∑ a, g (Sum.inl (some a)) • X.colP x τ a with hvW
  set vN := ∑ j, g (Sum.inr j) • col P (n' j) with hvN
  have hN : hermC τ.1 X.Gm vN vN = -∑ j, g (Sum.inr j) * conj (g (Sum.inr j)) :=
    hermC_sum_smul_col_negative_block τ.1 X.Gm P hP n' (fun j => rfl) (fun j => g (Sum.inr j))
  have hsum : vW + α0 • e = -vN := by
    calc vW + α0 • e = (α0 • e + vW + vN) - vN := by abel
      _ = -vN := by rw [hg, zero_sub]
  have hWe : hermC τ.1 X.Gm vW e = 0 := by
    rw [hvW, hermC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hermC_smul_left, ← hermC_conj τ.1 X.Gm_herm e, hperp a]
    simp
  have heW : hermC τ.1 X.Gm e vW = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm vW e, hWe, map_zero]
  have hexp : hermC τ.1 X.Gm (vW + α0 • e) (vW + α0 • e) =
      hermC τ.1 X.Gm vW vW + α0 * conj α0 * hermC τ.1 X.Gm e e := by
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hermC_smul_left, hermC_smul_left,
      hermC_smul_right, hermC_smul_right, hWe, heW]
    ring
  have hWW : hermC τ.1 X.Gm vW vW =
      ∑ a, ∑ b, g (Sum.inl (some a)) * X.gramPos x τ a b * conj (g (Sum.inl (some b))) := by
    rw [hvW]
    exact hermC_quad τ.1 X.Gm _ _
  have hNN : hermC τ.1 X.Gm (-vN) (-vN) = hermC τ.1 X.Gm vN vN := by
    rw [← neg_one_smul ℂ vN, hermC_smul_left, hermC_smul_right]
    simp
  have key : hermC τ.1 X.Gm vW vW + α0 * conj α0 * hermC τ.1 X.Gm e e =
      -∑ j, g (Sum.inr j) * conj (g (Sum.inr j)) := by
    rw [← hexp, hsum, hNN, hN]
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  have hq : 0 ≤ (hermC τ.1 X.Gm vW vW).re := by
    rw [hWW]
    exact quad_re_nonneg hpd.posSemidef _
  have ha : 0 ≤ Complex.normSq α0 * (hermC τ.1 X.Gm e e).re :=
    mul_nonneg (Complex.normSq_nonneg _) hneg
  have hs : 0 ≤ ∑ j, Complex.normSq (g (Sum.inr j)) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hq0 : (hermC τ.1 X.Gm vW vW).re = 0 := by linarith
  have hs0 : ∑ j, Complex.normSq (g (Sum.inr j)) = 0 := by linarith
  have hβ : ∀ j, g (Sum.inr j) = 0 := fun j => Complex.normSq_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hs0 j
      (Finset.mem_univ _))
  have hα : (fun a => g (Sum.inl (some a))) = 0 := by
    by_contra hne
    have h5 : 0 < (hermC τ.1 X.Gm vW vW).re := by
      rw [hWW]
      exact quad_re_pos hpd hne
    linarith
  have hvW0 : vW = 0 := by
    rw [hvW]
    exact Finset.sum_eq_zero fun a _ => by
      rw [show g (Sum.inl (some a)) = 0 from congrFun hα a, zero_smul]
  have hvN0 : vN = 0 := by
    rw [hvN]
    exact Finset.sum_eq_zero fun j _ => by rw [hβ j, zero_smul]
  have hα0 : α0 = 0 := by
    rw [hvW0, hvN0, add_zero, add_zero, smul_eq_zero] at hg
    exact hg.resolve_right he
  rcases i0 with (_ | a) | j
  · exact hi0 hα0
  · exact hi0 (congrFun hα a)
  · exact hi0 (hβ j)

theorem Hf_iso_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {e : Fin r → ℂ} (he : e ≠ 0)
    (hiso : hermC τ.1 X.Gm e e = 0) : 0 < (X.Hf x τ e e).re := by
  have hA := (X.gramPos_posDef hx τ).inv
  have hHf : X.Hf x τ e e = 2 * hermC τ.1 X.Gm (X.ppos x τ e) e := by
    rw [X.Hf_eq_two_ppos, hiso, sub_zero]
  rw [hHf, X.hermC_ppos_self]
  have hc0 : (fun a => hermC τ.1 X.Gm e (X.colP x τ a)) ≠ 0 := by
    intro h0
    have h3 := X.neg_of_perp hx τ he (fun b => congrFun h0 b)
    rw [hiso] at h3
    simp at h3
  have key := quad_re_pos hA hc0
  rw [show ∀ z : ℂ, (2 * z).re = 2 * z.re from fun z => by simp [Complex.mul_re]]
  exact mul_pos two_pos key

theorem ppos_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u + v) = X.ppos x τ u + X.ppos x τ v := by
  simp only [X.ppos_eq, hermC_add_left, add_mul, Finset.sum_add_distrib, add_smul]

theorem ppos_smul_eq (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (k • u) = k • X.ppos x τ u := by
  rw [X.ppos_eq, X.ppos_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_smul_left, mul_assoc]

theorem ppos_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  simp only [X.ppos_eq, hermC_sub_left, sub_mul, Finset.sum_sub_distrib, sub_smul]

theorem ppos_ppos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ (X.ppos x τ v) = X.ppos x τ v := by
  rw [X.ppos_eq x τ (X.ppos x τ v)]
  simp_rw [X.hermC_ppos_colP hx τ]
  exact (X.ppos_eq x τ v).symm

theorem hermC_ppos_right {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u (X.ppos x τ v) = hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ v) := by
  rw [X.ppos_eq x τ v, hermC_sum_right, hermC_sum_right]
  simp_rw [hermC_smul_right, X.hermC_ppos_colP hx τ]

theorem hermC_ppos_left {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) v = hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ v) := by
  rw [← hermC_conj τ.1 X.Gm_herm v (X.ppos x τ u), X.hermC_ppos_right hx τ v u,
    hermC_conj τ.1 X.Gm_herm]

noncomputable def jp (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ := (2 : ℂ) • X.ppos x τ v - v

theorem Hf_eq_jp (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm (X.jp x τ u) w := rfl

theorem Jz_apply (x : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) (τ : X.Ψ) :
    X.Jz x u τ = Complex.I • X.jp x τ (u τ) := rfl

theorem jp_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.jp x τ (u + v) = X.jp x τ u + X.jp x τ v := by
  show (2 : ℂ) • X.ppos x τ (u + v) - (u + v) =
    ((2 : ℂ) • X.ppos x τ u - u) + ((2 : ℂ) • X.ppos x τ v - v)
  rw [X.ppos_add, smul_add]
  abel

theorem jp_smul (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.jp x τ (k • u) = k • X.jp x τ u := by
  show (2 : ℂ) • X.ppos x τ (k • u) - k • u = k • ((2 : ℂ) • X.ppos x τ u - u)
  rw [X.ppos_smul_eq, smul_sub, smul_comm k (2 : ℂ)]

theorem jp_sub (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.jp x τ (u - v) = X.jp x τ u - X.jp x τ v := by
  show (2 : ℂ) • X.ppos x τ (u - v) - (u - v) =
    ((2 : ℂ) • X.ppos x τ u - u) - ((2 : ℂ) • X.ppos x τ v - v)
  rw [X.ppos_sub, smul_sub]
  abel

theorem jp_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.jp x τ (X.jp x τ v) = v := by
  show (2 : ℂ) • X.ppos x τ ((2 : ℂ) • X.ppos x τ v - v) - ((2 : ℂ) • X.ppos x τ v - v) = v
  rw [X.ppos_sub, X.ppos_smul_eq, X.ppos_ppos hx]
  have h : (2 : ℂ) • X.ppos x τ v - X.ppos x τ v = X.ppos x τ v := by
    rw [two_smul]
    abel
  rw [h]
  abel

theorem hermC_jp_left {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) v = hermC τ.1 X.Gm u (X.jp x τ v) := by
  show hermC τ.1 X.Gm ((2 : ℂ) • X.ppos x τ u - u) v =
    hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ v - v)
  rw [hermC_sub_left, hermC_smul_left, hermC_sub_right, hermC_smul_right,
    X.hermC_ppos_left hx τ u v, X.hermC_ppos_right hx τ u v]
  rw [map_ofNat]

theorem hermC_jp_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) (X.jp x τ v) = hermC τ.1 X.Gm u v := by
  rw [X.hermC_jp_left hx τ u (X.jp x τ v), X.jp_jp hx]

end Data

theorem hermC_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    hermC τ G (Data.emb τ u) (Data.emb τ v) = τ (herm G u v) := by
  unfold hermC herm Data.emb
  simp only [map_sum, map_mul, emb_cc]

theorem emb_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    {u : Fin r → E} (hu : u ≠ 0) : Data.emb τ u ≠ 0 := by
  intro h
  apply hu
  funext a
  have h1 := congrFun h a
  simp only [Data.emb, Pi.zero_apply] at h1
  exact (map_eq_zero τ).1 h1

end ReciprocityTheory.ChartRestriction.G.FD

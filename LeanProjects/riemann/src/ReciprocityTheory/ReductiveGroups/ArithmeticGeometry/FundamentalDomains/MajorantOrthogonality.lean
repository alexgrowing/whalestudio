import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermCOrthonormalCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCombinations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPairingAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec

namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def pform (X : Data E r) : ReciprocityTheory.MultiplicativeHeights.HermForm E r where
  c := (IsCMField.complexConj E).toAlgHom.toRingHom
  c_invol x := IsCMField.complexConj_apply_apply E x
  c_emb σ x := IsCMField.complexEmbedding_complexConj E σ x
  G := X.Gmᵀ
  G_herm a b := X.Gm_herm b a

lemma pform_h (X : Data E r) (x y : Fin r → E) : (pform X).h x y = herm X.Gm y x := by
  change ∑ a, ∑ b, cc (x a) * X.Gm b a * y b = ∑ a, ∑ b, y a * X.Gm a b * cc (x b)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma isLattice (X : DataX E r) : ReciprocityTheory.MultiplicativeHeights.IsLattice X.L' := by
  refine ⟨X.L'_fg, ?_⟩
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro v hv
  have h := X.NA_sub v hv
  have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
  have hv' : v = (X.NA : E)⁻¹ • ((X.NA : E) • v) := by
    rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
  rw [hv']
  exact Submodule.smul_mem _ _ (Submodule.subset_span h)

lemma selfDual (X : DataX E r) : ReciprocityTheory.MultiplicativeHeights.IsSelfDual (pform X.toData) X.L' := by
  have key : ∀ x y, (pform X.toData).h x y = cc (herm X.Gm x y) := fun x y => by
    rw [pform_h, ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm X.Gm_herm]
  have toI : ∀ z : E, IsIntegral ℤ z → ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have ofI : ∀ z : E, ReciprocityTheory.MultiplicativeHeights.IsIntegralElt z → IsIntegral ℤ z := by
    rintro z ⟨o, rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe o
  have ccI : ∀ z : E, IsIntegral ℤ z → IsIntegral ℤ (cc z) := fun z hz =>
    hz.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  refine ⟨fun x hx y hy => ?_, fun x hx => X.L'_dual x fun y hy => ?_⟩
  · rw [key]
    exact toI _ (ccI _ (X.L'_int x hx y hy))
  · have h1 := hx y hy
    rw [key] at h1
    have h2 := ccI _ (ofI _ h1)
    simpa [cc, IsCMField.complexConj_apply_apply] using h2

private lemma sum_inv_mulVec_smul_col_of_det_ne_zero (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (w : Fin r → ℂ) :
    ∑ k, (M⁻¹ *ᵥ w) k • col M k = w := by
  have h2 : M *ᵥ (M⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  conv_rhs => rw [← h2]
  funext i
  simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]

private lemma hermC_col_mat_of_isOrtho (X : Data E r) {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (k l : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) k) (col (mat x τ) l) =
      if k = l then (if (k : ℕ) < X.p0 then (1 : ℂ) else -1) else 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ortho_apply (X := X) ho τ k l]
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : (k : ℕ) < X.p0
    · simp [hk, sgn]
    · simp [hk, sgn]
  · simp [hkl]

lemma maj_ortho (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (v : Fin r → ℂ) : X.maj x τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x τ)⁻¹ *ᵥ v) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  set c := (mat x τ)⁻¹ *ᵥ v with hc
  have hv : v = ∑ k, c k • col (mat x τ) k := (sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet v).symm
  have hcol : ∀ a, col (mat x τ) a = ∑ l, (Pi.single a 1 : Fin r → ℂ) l • col (mat x τ) l := by
    intro a
    simp [Pi.single_apply]
  have hpair : ∀ a : Fin r, hermC τ.1 X.Gm v (col (mat x τ) a) = ReciprocityTheory.MultiplicativeHeights.sgn X.p0 a * c a := by
    intro a
    rw [hv, hcol a, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]
    simp [ReciprocityTheory.MultiplicativeHeights.jForm, Pi.single_apply, apply_ite]
  have hgp : X.gramPos x τ = 1 := by
    unfold Data.gramPos
    rw [ho τ]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply, sgn, a.isLt]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hab, Fin.castLE_inj]
  have hpos : X.posPart x τ v = ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 := by
    unfold Data.posPart
    rw [hgp, inv_one]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hpair]
    simp [ReciprocityTheory.MultiplicativeHeights.sgn]
  have hself : (hermC τ.1 X.Gm v v).re = ∑ k : Fin r, (if (k : ℕ) < X.p0 then (1 : ℝ) else -1) * ‖c k‖ ^ 2 := by
    rw [hv, ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf]
    simp only [ReciprocityTheory.MultiplicativeHeights.jForm, Complex.re_sum, ReciprocityTheory.MultiplicativeHeights.sgn]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul']
    have hre : (((‖c k‖ : ℝ) : ℂ) ^ 2).re = ‖c k‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    split_ifs <;> simp [hre]
  unfold Data.maj
  rw [hpos, hself]
  unfold ReciprocityTheory.MultiplicativeHeights.normSq
  have hsplit : ∑ a : Fin X.p0, ‖c (Fin.castLE X.p0_le a)‖ ^ 2 =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then ‖c k‖ ^ 2 else 0 :=
    Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _
      (fun k hk => by
        rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩)
      (fun a => by simp [a.isLt])
  rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma herm_coord (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (u v : Fin r → E) : τ.1 (herm X.Gm u v) = ReciprocityTheory.MultiplicativeHeights.jForm X.p0
      ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) := by
  classical
  have hdet : (mat x τ).det ≠ 0 := ((Data.mem_dom_iff X x).mp hx τ).1
  have hf := hermC_col_mat_of_isOrtho X ho τ
  have h1 : τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := by
    simp only [herm, hermC, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]
  calc τ.1 (herm X.Gm u v) = hermC τ.1 X.Gm (Data.emb τ.1 u) (Data.emb τ.1 v) := h1
    _ = hermC τ.1 X.Gm (∑ k, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) k • col (mat x τ) k)
          (∑ l, ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) l • col (mat x τ) l) := by
        rw [sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet, sum_inv_mulVec_smul_col_of_det_ne_zero (mat x τ) hdet]
    _ = _ := ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.hC_comb2_ortho τ.1 X.Gm _ hf _ _

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality

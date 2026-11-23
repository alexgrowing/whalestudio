import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadHol
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks

noncomputable section

open MeasureTheory Matrix Set
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def epsM (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem epsM_mul_self : epsM n * epsM n = 1 := by
  simp [epsM, fromBlocks_multiply, ← fromBlocks_one]

def epsU (n : ℕ) : GL (Fin n ⊕ Fin n) ℂ := ⟨epsM n, epsM n, epsM_mul_self, epsM_mul_self⟩

theorem eps_conj_blocks (M : M2 n) :
    epsM n * M * epsM n = fromBlocks M.toBlocks₁₁ (-M.toBlocks₁₂) (-M.toBlocks₂₁) M.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [epsM, fromBlocks_multiply]

theorem epsM_conjTranspose : (epsM n)ᴴ = epsM n := by
  simp [epsM, fromBlocks_conjTranspose]

theorem eps_JJ : epsM n * JJ n * epsM n = -JJ n := by
  simp [epsM, JJ, fromBlocks_multiply, fromBlocks_neg]

theorem inG_eps_conj {M : M2 n} (h : InG M) : InG (epsM n * M * epsM n) := by
  unfold InG at h ⊢
  have e4 : ∀ X : M2 n, epsM n * (JJ n * (epsM n * X)) = -(JJ n * X) := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eps_JJ, Matrix.neg_mul]
  have h' : ∀ X : M2 n, Mᴴ * (JJ n * (M * X)) = JJ n * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
  simp only [conjTranspose_mul, epsM_conjTranspose, Matrix.mul_assoc]
  rw [e4, Matrix.mul_neg, Matrix.mul_neg, h', ← Matrix.mul_assoc, eps_JJ, neg_neg]

def cHom (n : ℕ) : GR n →* GR n where
  toFun y := ⟨epsU n * y.1 * epsU n, by
    show InG ((epsU n * y.1 * epsU n : GL (Fin n ⊕ Fin n) ℂ) : M2 n)
    simpa [epsU] using inG_eps_conj (n := n) y.2⟩
  map_one' := by
    ext : 2
    simp [epsU, epsM_mul_self]
  map_mul' x y := by
    ext : 2
    simp only [Subgroup.coe_mul, Units.val_mul]
    have h := epsM_mul_self (n := n)
    simp only [epsU, Units.val_mk]
    calc epsM n * (x.1.1 * y.1.1) * epsM n = epsM n * x.1.1 * (epsM n * epsM n) * y.1.1 * epsM n := by
          rw [h]; simp [Matrix.mul_assoc]
      _ = epsM n * x.1.1 * epsM n * (epsM n * y.1.1 * epsM n) := by simp [Matrix.mul_assoc]

theorem mR_c (y : GR n) : mR (cHom n y) = epsM n * mR y * epsM n := rfl

theorem cHom_cHom (y : GR n) : cHom n (cHom n y) = y := by
  apply Subtype.ext
  apply Units.ext
  show mR (cHom n (cHom n y)) = mR y
  rw [mR_c, mR_c]
  have h := epsM_mul_self (n := n)
  calc epsM n * (epsM n * mR y * epsM n) * epsM n = (epsM n * epsM n) * mR y * (epsM n * epsM n) := by
        simp only [Matrix.mul_assoc]
    _ = mR y := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem cHom_cont : Continuous (cHom n) := by
  show Continuous fun y : GR n => (⟨epsU n * y.1 * epsU n, _⟩ : GR n)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem first_cayley_block_of_conjugation (y : GR n) : u1 (mR (cHom n y)) = u2 (mR y) := by
  rw [mR_c, u1, u2, eps_conj_blocks]
  simp

theorem second_cayley_block_of_conjugation (y : GR n) : u2 (mR (cHom n y)) = u1 (mR y) := by
  rw [mR_c, eps_conj_blocks]
  simp [u1, u2]

theorem det_c (y : GR n) : (mR (cHom n y)).det = (mR y).det := by
  have h := congrArg Matrix.det (epsM_mul_self (n := n))
  rw [det_mul, det_one] at h
  rw [mR_c, det_mul, det_mul]
  calc (epsM n).det * (mR y).det * (epsM n).det = (mR y).det * ((epsM n).det * (epsM n).det) := by ring
    _ = (mR y).det := by rw [h, mul_one]

theorem spherical_section_conjugation_swap (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e (cHom n y) = F0 q p e y := by
  simp only [F0, f0, det_c, first_cayley_block_of_conjugation, second_cayley_block_of_conjugation]
  ring

theorem norm_sq_det_cayley_blocks_eq (M : M2 n) (h : InG M) : ‖(u1 M).det‖ ^ 2 = ‖(u2 M).det‖ ^ 2 := by
  have hJ2 : JJ n * JJ n = -1 := by
    simp only [JJ, fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  unfold InG at h
  have hL : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    calc -(JJ n * Mᴴ * JJ n) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ2, neg_neg]
  have hR : M * (-(JJ n * Mᴴ * JJ n)) = 1 := mul_eq_one_comm.1 hL
  have hMJ : M * JJ n * Mᴴ = JJ n := by
    calc M * JJ n * Mᴴ = M * (-(JJ n * Mᴴ * JJ n)) * JJ n := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ2, Matrix.mul_one, neg_neg]
      _ = JJ n := by rw [hR, Matrix.one_mul]
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (fromBlocks_toBlocks M).symm
  rw [hM] at hMJ
  have hb := congrArg toBlocks₂₂ hMJ
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at hb
  have key : M.toBlocks₂₁ * (M.toBlocks₂₂)ᴴ = M.toBlocks₂₂ * (M.toBlocks₂₁)ᴴ := by
    rw [← sub_eq_zero, ← hb]
    abel
  have e1 : u1 M * (u1 M)ᴴ = u2 M * (u2 M)ᴴ := by
    simp [u1, u2, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, key]
    abel
  have hn : ∀ u : Matrix (Fin n) (Fin n) ℂ, ((‖u.det‖ ^ 2 : ℝ) : ℂ) = (u * uᴴ).det := by
    intro u
    simp [det_mul, det_conjTranspose, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  rw [hn, hn, e1]

theorem hLoc_c (y : GR n) : hLoc (cHom n y) = hLoc y := by
  simp only [hLoc, first_cayley_block_of_conjugation]
  rw [norm_sq_det_cayley_blocks_eq (mR y) y.2]

theorem zkey (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) :
    (Complex.I • c + d)ᴴ * (Complex.I • a - b) = -((Complex.I • a + b)ᴴ * (-(Complex.I • c) + d)) := by
  rw [eq_neg_iff_add_eq_zero]
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have h1 : aᴴ * c = cᴴ * a := sub_eq_zero.1 E1
  have h3 : bᴴ * d = dᴴ * b := sub_eq_zero.1 E3
  have h2 : aᴴ * d = 1 + cᴴ * b := by
    rw [← E2]
    abel
  have h4 : dᴴ * a = 1 + bᴴ * c := by
    rw [← E2']
    abel
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [h1, h3, h2, h4]
  simp only [smul_add]
  abel

private theorem eq_zero_of_star_dotProduct_self_eq_zero (v : Fin n → ℂ) (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have e : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.conj_mul']
  rw [e] at h
  have h' : ∑ i, ‖v i‖ ^ 2 = 0 := by exact_mod_cast h
  have h'' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).1 h'
  funext i
  simpa using h'' i (Finset.mem_univ i)

private theorem card_fromBlocks_cayley_eq_mul (M : M2 n) (h : InG M) :
    -((M.toBlocks₂₁)ᴴ * M.toBlocks₁₁) + (M.toBlocks₁₁)ᴴ * M.toBlocks₂₁ = 0 ∧
    -((M.toBlocks₂₁)ᴴ * M.toBlocks₁₂) + (M.toBlocks₁₁)ᴴ * M.toBlocks₂₂ = 1 ∧
    -((M.toBlocks₂₂)ᴴ * M.toBlocks₁₂) + (M.toBlocks₁₂)ᴴ * M.toBlocks₂₂ = 0 := by
  have hM := (fromBlocks_toBlocks M).symm
  unfold InG at h
  rw [hM] at h
  have h11 := congrArg toBlocks₁₁ h
  have h12 := congrArg toBlocks₁₂ h
  have h22 := congrArg toBlocks₂₂ h
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h11 h12 h22
  exact ⟨h11, h12, h22⟩

private theorem conjTranspose_I_smul_add_sub_eq_two_I (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : -(cᴴ * a) + aᴴ * c = 0)
    (E2 : -(cᴴ * b) + aᴴ * d = 1) (E3 : -(dᴴ * b) + bᴴ * d = 0) :
    (Complex.I • c + d)ᴴ * (Complex.I • a + b) - (Complex.I • a + b)ᴴ * (Complex.I • c + d) =
      (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have := congrArg conjTranspose E2
    simp [conjTranspose_add, conjTranspose_neg, conjTranspose_mul] at this
    rw [sub_eq_neg_add]
    exact this
  have h1 : aᴴ * c = cᴴ * a := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact E1
  have h3 : bᴴ * d = dᴴ * b := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact E3
  have h2 : aᴴ * d = 1 + cᴴ * b := by
    rw [← E2]
    abel
  have h4 : dᴴ * a = 1 + bᴴ * c := by
    rw [← E2']
    abel
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h3, h2, h4]
  simp only [smul_add]
  module

private theorem det_u1_ne_zero_of_inG (M : M2 n) (h : InG M) : (u1 M).det ≠ 0 := by
  obtain ⟨h11, h12, h22⟩ := card_fromBlocks_cayley_eq_mul M h
  intro hdet
  obtain ⟨v, hv, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have W := conjTranspose_I_smul_add_sub_eq_two_I _ _ _ _ h11 h12 h22
  have hu' : (Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂) *ᵥ v = 0 := hu
  have hz : star v ⬝ᵥ (((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) = 0 := by
    rw [← W, Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu',
      Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hu', star_zero,
      zero_dotProduct]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at hz
  rcases hz with h0 | h0
  · simp [Complex.I_ne_zero] at h0
  · exact hv (eq_zero_of_star_dotProduct_self_eq_zero v h0)

private theorem det_u2_ne_zero_of_inG (M : M2 n) (h : InG M) : (u2 M).det ≠ 0 := by
  have e : u2 M = u1 (epsM n * M * epsM n) := by
    rw [u1, u2, eps_conj_blocks]
    simp
  rw [e]
  exact det_u1_ne_zero_of_inG _ (inG_eps_conj h)

theorem zOf_c (y : GR n) : zOf (cHom n y) = -(zOf y)ᴴ := by
  have hy : InG (mR y) := y.2
  obtain ⟨h11, h12, h22⟩ := card_fromBlocks_cayley_eq_mul (mR y) hy
  have hU1 := det_u1_ne_zero_of_inG (mR y) hy
  have hU2 := det_u2_ne_zero_of_inG (mR y) hy
  have zk := zkey (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ (mR y).toBlocks₂₁ (mR y).toBlocks₂₂
    (by rw [sub_eq_neg_add]; exact h11) (by rw [sub_eq_neg_add]; exact h12)
    (by rw [sub_eq_neg_add]; exact h22)
  simp only [zOf, first_cayley_block_of_conjugation]
  rw [mR_c, eps_conj_blocks]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
  rw [conjTranspose_mul, conjTranspose_nonsing_inv]
  have hU1h : IsUnit ((u1 (mR y))ᴴ).det := by
    rw [det_conjTranspose]
    exact (isUnit_iff_ne_zero.2 hU1).star
  have hU2' : IsUnit (u2 (mR y)).det := isUnit_iff_ne_zero.2 hU2
  have zk' : (u1 (mR y))ᴴ * (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂) =
      -((Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ * u2 (mR y)) := by
    rw [← sub_eq_add_neg]
    exact zk
  calc (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂) * (u2 (mR y))⁻¹
      = ((u1 (mR y))ᴴ)⁻¹ * ((u1 (mR y))ᴴ * (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂)) *
          (u2 (mR y))⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU1h, Matrix.one_mul]
    _ = ((u1 (mR y))ᴴ)⁻¹ * (-((Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ * u2 (mR y))) *
          (u2 (mR y))⁻¹ := by rw [zk']
    _ = -(((u1 (mR y))ᴴ)⁻¹ * (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ) := by
        rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hU2', Matrix.mul_one]

theorem herm_neg (x : Fin n → Fin n → ℝ) : herm (-x) = -herm x := by
  ext i j
  simp [herm]
  ring

theorem eps_nU (B : Matrix (Fin n) (Fin n) ℂ) : epsM n * nU B * epsM n = nU (-B) := by
  rw [eps_conj_blocks]
  simp [nU]

theorem singTest_neg {ψ : (Fin n → Fin n → ℝ) → ℂ} (h : IsSingTest ψ) : IsSingTest (fun x => ψ (-x)) := by
  refine ⟨h.1.comp continuous_neg, h.2.1.comp_homeomorph (Homeomorph.neg _), fun β hβ hdet => ?_⟩
  have e : ∀ x, eTr β x = eTr (-β) (-x) := by
    intro x
    simp [eTr, herm_neg]
  simp_rw [e]
  rw [integral_neg_eq_self (fun x => ψ x * eTr (-β) x) volume]
  exact h.2.2 (-β) hβ.neg (by rw [det_neg, hdet, mul_zero])

theorem conj : Conj := by
  intro hh m n p q e hm hmn hpq G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hf U d Ê t hU hR hs hD hC hE j hj hsing g
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq] at hf
    rw [hp, hq]
    exact hh m n e hm hmn G Pp Γ ι s₀ Ht f hι hf U d Ê t hU hR hs hD hC hE j hj hsing g
  · rw [hp, hq] at hf
    rw [hp, hq]
    have hm0 : m ≠ 0 := by omega
    have hf' : ∀ g' : G, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g' = x * (ι.comp (cHom n)) y ∧
        ∀ y' : GR n, ((Ht (x * (ι.comp (cHom n)) y') : ℝ) = r * hLoc y' ∧
          f (x * (ι.comp (cHom n)) y') = S * F0 m 0 e y') := by
      intro g'
      obtain ⟨x, y, S, r, hr, hg, hy⟩ := hf g'
      refine ⟨x, cHom n y, S, r, hr, ?_, fun y' => ?_⟩
      · simp [hg, cHom_cHom]
      · obtain ⟨h1, h2⟩ := hy (cHom n y')
        refine ⟨?_, ?_⟩
        · simpa [hLoc_c] using h1
        · simpa [spherical_section_conjugation_swap] using h2
    have hs' : ∀ ψ : (Fin n → Fin n → ℝ) → ℂ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n,
        (∀ x, mR (nb x) = nU (herm x)) → ∀ (g' : G) (a b : GR n),
          ∫ x, iteratedDeriv j (fun s => Ê s (g' * (ι.comp (cHom n)) (a * nb x * b))) s₀ * ψ x = 0 := by
      intro ψ hψ nb hnb g' a b
      have hnb' : ∀ x, mR (cHom n (nb (-x))) = nU (herm x) := by
        intro x
        rw [mR_c, hnb, herm_neg, eps_nU, neg_neg]
      have h0 := hsing (fun x => ψ (-x)) (singTest_neg hψ) (fun x => cHom n (nb (-x))) hnb' g'
        (cHom n a) (cHom n b)
      rw [← integral_neg_eq_self]
      simpa [map_mul] using h0
    obtain ⟨H, hH, hrep⟩ := hh m n e hm hmn G Pp Γ (ι.comp (cHom n)) s₀ Ht f (hι.comp cHom_cont) hf' U d Ê t
      hU hR hs hD hC hE j hj hs' g
    refine ⟨H, hH, fun y => ?_⟩
    have h1 := hrep (cHom n y)
    simp only [MonoidHom.comp_apply, cHom_cHom, spherical_section_conjugation_swap, zOf_c] at h1
    show iteratedDeriv j (fun x => Ê x (g * ι y)) s₀ = _
    rw [h1]
    simp [hm0]

end PositivityTheory.Rg.Sw.HSt

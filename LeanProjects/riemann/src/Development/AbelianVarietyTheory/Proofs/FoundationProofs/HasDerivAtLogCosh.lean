import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DilMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialKFiniteBothMembers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd

noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues Matrix

variable {p q n : ℕ}

theorem rectDiag_mul_ct (f g : ℕ → ℝ) (hf : ∀ i, min p q ≤ i → f i = 0) :
    rectDiag p q f * (rectDiag p q g)ᴴ = Matrix.diagonal fun i : Fin p => ((f i * g i : ℝ) : ℂ) := by
  ext i k
  simp only [rectDiag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hi : (i : ℕ) < q
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · by_cases h : i = k
      · subst h; simp
      · have : (k : ℕ) ≠ i := fun e => h (Fin.ext e.symm)
        simp [h, this]
    · intro j _ hj
      have : (i : ℕ) ≠ j := fun e => hj (Fin.ext e.symm)
      simp [this]
    · simp
  · simp [hf i (by omega)]

theorem ct_mul_rectDiag (f g : ℕ → ℝ) (hf : ∀ i, min p q ≤ i → f i = 0) :
    (rectDiag p q f)ᴴ * rectDiag p q g = Matrix.diagonal fun i : Fin q => ((f i * g i : ℝ) : ℂ) := by
  have h : ∀ f : ℕ → ℝ, (rectDiag p q f)ᴴ = rectDiag q p f := by
    intro f; ext i j
    simp only [rectDiag, Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases e : (j : ℕ) = i
    · simp [e]
    · simp [e, Ne.symm e]
  have := rectDiag_mul_ct (p := q) (q := p) f g (by rwa [min_comm])
  rwa [← h f, ← h g, Matrix.conjTranspose_conjTranspose] at this

theorem hasDerivAt_hyperbolicMatrix (σ : ℕ → ℝ) (hσ : ∀ i, min p q ≤ i → σ i = 0) (t : ℝ) (a b : Ix p q) :
    HasDerivAt (fun t => hypMat p q σ t a b) ((diagP p q σ * hypMat p q σ t) a b) t := by
  have hc : ∀ i, HasDerivAt (fun t : ℝ => ((Real.cosh (t * σ i) : ℝ) : ℂ))
      ((σ i * Real.sinh (t * σ i) : ℝ) : ℂ) t := fun i =>
    (((hasDerivAt_id t).mul_const (σ i)).cosh.congr_deriv (by simp [mul_comm])).ofReal_comp
  have hs : ∀ i, HasDerivAt (fun t : ℝ => ((Real.sinh (t * σ i) : ℝ) : ℂ))
      ((σ i * Real.cosh (t * σ i) : ℝ) : ℂ) t := fun i =>
    (((hasDerivAt_id t).mul_const (σ i)).sinh.congr_deriv (by simp [mul_comm])).ofReal_comp
  simp only [diagP, hypMat, Matrix.fromBlocks_multiply, Matrix.zero_mul, zero_add, add_zero,
    rectDiag_mul_ct _ _ hσ, ct_mul_rectDiag _ _ hσ]
  rcases a with a | a <;> rcases b with b | b
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply]
    split_ifs
    · exact hc a
    · exact hasDerivAt_const _ _
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.mul_diagonal, rectDiag, Matrix.of_apply]
    split_ifs with h
    · rw [← h, ← Complex.ofReal_mul]; exact hs a
    · rw [zero_mul]; exact hasDerivAt_const _ _
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.mul_diagonal, rectDiag, Matrix.of_apply,
      Matrix.conjTranspose_apply]
    split_ifs with h
    · simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]; exact hs b
    · rw [star_zero, zero_mul]; exact hasDerivAt_const _ _
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
    split_ifs
    · exact hc a
    · exact hasDerivAt_const _ _

theorem hypMat_zero (σ : ℕ → ℝ) : hypMat p q σ 0 = 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [hypMat, rectDiag, Matrix.one_apply]

open scoped Matrix.Norms.Operator in
theorem exp_diagP (σ : ℕ → ℝ) (hσ : ∀ i, min p q ≤ i → σ i = 0) (t : ℝ) :
    NormedSpace.exp (t • diagP p q σ) = hypMat p q σ t := by
  set X := diagP p q σ with hX
  have hG : ∀ t, HasDerivAt (hypMat p q σ) (X * hypMat p q σ t) t := fun t =>
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hasDerivAt_hyperbolicMatrix σ hσ t a b
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-X)) * hypMat p q σ t) 0 t := by
    intro t
    refine ((hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) t).fun_mul (hG t)).congr_deriv ?_
    simp [mul_assoc]
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  rw [zero_smul, NormedSpace.exp_zero, hypMat_zero, one_mul] at h
  have h2 : NormedSpace.exp (t • X) * NormedSpace.exp (t • (-X)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (by rw [smul_neg]; exact (Commute.refl _).neg_right), smul_neg,
      add_neg_cancel, NormedSpace.exp_zero]
  rw [← mul_one (NormedSpace.exp (t • X)), ← h, ← mul_assoc, h2, one_mul]

theorem exists_gauss (σ : ℕ → ℝ) (hσ : ∀ i, min p q ≤ i → σ i = 0) (t : ℝ) :
    ∃ (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ),
      hypMat p q σ t * (diagP p q σ + tanhDiag p q σ t - Matrix.fromBlocks 0 0 C 0) =
        Matrix.fromBlocks 0 B 0 0 * hypMat p q σ t := by
  refine ⟨rectDiag p q fun i => σ i / Real.cosh (t * σ i) ^ 2,
    (rectDiag p q fun i => σ i * (1 + Real.tanh (t * σ i) ^ 2))ᴴ, ?_⟩
  have e : diagP p q σ + tanhDiag p q σ t -
      Matrix.fromBlocks 0 0 (rectDiag p q fun i => σ i * (1 + Real.tanh (t * σ i) ^ 2))ᴴ 0 =
      Matrix.fromBlocks (Matrix.diagonal fun i : Fin p => ((σ i * Real.tanh (t * σ i) : ℝ) : ℂ))
        (rectDiag p q σ) (rectDiag p q fun i => -(σ i * Real.tanh (t * σ i) ^ 2))ᴴ
        (Matrix.diagonal fun i : Fin q => ((-(σ i * Real.tanh (t * σ i)) : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [diagP, tanhDiag, Matrix.diagonal_apply, posIx]
    · simp [diagP, tanhDiag]
    · simp only [diagP, tanhDiag, Matrix.sub_apply, Matrix.add_apply, Matrix.fromBlocks_apply₂₁, rectDiag,
        Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [Matrix.diagonal_apply_ne _ (by simp)]
      split_ifs with h1
      · simp only [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
      · simp
    · simp [diagP, tanhDiag, Matrix.diagonal_apply, posIx]
  have hs : ∀ i, min p q ≤ i → Real.sinh (t * σ i) = 0 := fun i hi => by simp [hσ i hi]
  have hb : ∀ i, min p q ≤ i → σ i / Real.cosh (t * σ i) ^ 2 = 0 := fun i hi => by simp [hσ i hi]
  have hch : ∀ i, Real.cosh (t * σ i) ≠ 0 := fun i => (Real.cosh_pos _).ne'
  rw [e]
  simp only [hypMat, Matrix.fromBlocks_multiply, Matrix.zero_mul, zero_add, add_zero,
    rectDiag_mul_ct _ _ hs, ct_mul_rectDiag _ _ hs, rectDiag_mul_ct _ _ hb, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]
  congr 1
  · congr 1
    funext i
    norm_cast
    have := hch i
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    rw [Real.cosh_sq]; ring
  · ext i j
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, rectDiag, Matrix.of_apply]
    split_ifs with h
    · rw [← h]
      norm_cast
      have := hch i
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      rw [Real.cosh_sq]; ring
    · simp
  · ext i j
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, rectDiag, Matrix.of_apply,
      Matrix.conjTranspose_apply, Matrix.zero_apply]
    split_ifs with h
    · simp only [Complex.star_def, Complex.conj_ofReal, ← h]
      norm_cast
      have := hch j
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      ring
    · simp
  · rw [← Matrix.diagonal_zero]
    congr 1
    funext i
    norm_cast
    have := hch i
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring

theorem pderiv_dil (u : Ix p q → ℝ) (l : Ln p q n 0) (P : Pol p q n 0) :
    MvPolynomial.pderiv l (dil n u P) = ((Real.exp (u l.1) : ℝ) : ℂ) • dil n u (MvPolynomial.pderiv l P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add]
  | monomial α c =>
    rw [dil_monomial, Derivation.map_smul, MvPolynomial.pderiv_monomial, dil_monomial, smul_smul]
    by_cases h : α l = 0
    · simp [h]
    · congr 1
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      have : ∀ l' : Ln p q n 0, ((α l' : ℝ) + 1 / 2) * u l'.1 =
          (if l' = l then u l.1 else 0) + ((((α - Finsupp.single l 1 : Ln p q n 0 →₀ ℕ) l' : ℕ) : ℝ) + 1 / 2) * u l'.1 := by
        intro l'
        split_ifs with e
        · subst e
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub (Nat.pos_of_ne_zero h)]
          push_cast; ring
        · simp [Finsupp.single_apply, Ne.symm e]
      rw [Finset.sum_congr rfl fun l' _ => this l', Finset.sum_add_distrib]
      simp

theorem killed_dil (u : Ix p q → ℝ) {Φ : Pol p q n 0} (h : KilledByPMinus Φ) : KilledByPMinus (dil n u Φ) := by
  intro a b
  have := h a b
  simp only [lowerOp] at this ⊢
  simp only [pderiv_dil, Derivation.map_smul, ← Finset.smul_sum, ← map_sum, this, map_zero, smul_zero]

theorem norm_sq_sum {σ H : Type} [DecidableEq σ] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (h : IsFockIP ι) (S : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℂ) :
    ‖∑ α ∈ S, c α • ι (MvPolynomial.monomial α 1)‖ ^ 2 =
      ∑ α ∈ S, ‖c α‖ ^ 2 * ‖ι (MvPolynomial.monomial α 1)‖ ^ 2 := by
  apply Complex.ofReal_injective
  have e : ∀ x : H, ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e, sum_inner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [inner_sum, Finset.sum_eq_single α, ← mul_pow, ← norm_smul, e]
  · intro β _ hβ
    rw [inner_smul_left, inner_smul_right, h, if_neg (Ne.symm hβ), mul_zero, mul_zero]
  · exact fun h => (h hα).elim

theorem norm_dil_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Pol p q n 0 →ₗ[ℂ] H}
    (h : IsFockIP ι) (u : Ix p q → ℝ) (hu : ∀ a, 0 ≤ u a) (Φ : Pol p q n 0) :
    ‖ι (dil n (-u) Φ)‖ ≤ Real.exp (-((∑ l : Ln p q n 0, u l.1) / 2)) * ‖ι Φ‖ := by
  have e : ∀ (α : Ln p q n 0 →₀ ℕ) (c : ℂ), (MvPolynomial.monomial α c : Pol p q n 0) =
      c • MvPolynomial.monomial α 1 := fun α c => by simp [MvPolynomial.smul_monomial]
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow]
  conv_lhs => rw [Φ.as_sum]
  conv_rhs => rw [Φ.as_sum]
  simp only [map_sum, dil_monomial, e _ (MvPolynomial.coeff _ _), smul_smul, map_smul, norm_sq_sum h,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [norm_mul, ← mul_assoc, ← mul_pow (Real.exp _), mul_comm (Real.exp _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  gcongr
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 := hu l.1
  have h2 : (0 : ℝ) ≤ α l := Nat.cast_nonneg _
  simp only [Pi.neg_apply]
  nlinarith [mul_nonneg h1 h2]

theorem exp_sum_logCosh (σ : ℕ → ℝ) (hσ : ∀ i, min p q ≤ i → σ i = 0) :
    Real.exp (-((∑ l : Ln p q n 0, Real.log (Real.cosh (σ (posIx l.1)))) / 2)) =
      ∏ i : Fin (min p q), Real.cosh (σ i) ^ (-(n : ℤ)) := by
  have h : ∀ m, min p q ≤ m → ∑ i : Fin m, Real.log (Real.cosh (σ i)) =
      ∑ i : Fin (min p q), Real.log (Real.cosh (σ i)) := by
    intro m hm
    rw [Fin.sum_univ_eq_sum_range (fun i => Real.log (Real.cosh (σ i))),
      Fin.sum_univ_eq_sum_range (fun i => Real.log (Real.cosh (σ i)))]
    refine (Finset.sum_subset (Finset.range_subset_range.2 hm) fun i _ hi => ?_).symm
    simp [hσ i (not_lt.1 fun h => hi (Finset.mem_range.2 h))]
  have e : -((∑ l : Ln p q n 0, Real.log (Real.cosh (σ (posIx l.1)))) / 2) =
      ∑ i : Fin (min p q), Real.log (Real.cosh (σ i)) * ((-(n : ℤ) : ℤ) : ℝ) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, add_zero, nsmul_eq_mul,
      ← Finset.mul_sum, Fintype.sum_sum_type, posIx, Sum.elim_inl, Sum.elim_inr, h p (min_le_left _ _),
      h q (min_le_right _ _)]
    push_cast
    ring
  rw [e, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_def_of_pos (Real.cosh_pos _), Real.rpow_intCast]

theorem exists_conj_diagP (T : GrpData p q) {X : Mat p q} (hX : X ∈ pR p q) :
    ∃ σ : ℕ → ℝ, (∀ i, min p q ≤ i → σ i = 0) ∧ (∀ i : Fin (min p q), σ i = singVal X i) ∧
      ∃ k ∈ T.Kset, X * matG T k = matG T k * diagP p q σ := by
  obtain ⟨B, rfl⟩ := exists_pY hX
  set L := Matrix.toEuclideanLin (Matrix.of B) with hL
  refine ⟨fun i => L.singularValues i, fun i hi => ?_, fun i => rfl, ?_⟩
  · by_contra h
    have h1 : i ∈ L.singularValues.support := Finsupp.mem_support_iff.mpr h
    rw [L.support_singularValues, Finset.mem_range] at h1
    have h2 := Submodule.finrank_le (LinearMap.range L)
    have h3 := LinearMap.finrank_range_le L
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h2 h3
    omega
  obtain ⟨U, hU, V, hV, h⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q (Matrix.of B)
  change Matrix.of B = U * rectDiag p q (fun i => L.singularValues i) * Vᴴ at h
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  let g : GL (Ix p q) ℂ := ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
    by simp [Matrix.fromBlocks_multiply, hU2, hV2], by simp [Matrix.fromBlocks_multiply, hU1, hV1]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    change (Matrix.fromBlocks U 0 0 V)ᴴ * Jm p q * Matrix.fromBlocks U 0 0 V = Jm p q
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU1, hV1]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : Mat p q).det) two_pos
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by rw [matG, hk]
  refine ⟨k, ?_, ?_⟩
  · change IsKC (matG T k)
    rw [hm]
    intro a b hab
    cases a <;> cases b <;> first | rfl | exact (hab trivial).elim
  · rw [hm, pY, pOf, h, diagP]
    simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, hU1, hV1]

end GlobalTheory.FockDecay
end

noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.FockAlg GlobalTheory.RealPar Matrix

variable {p q r s : ℕ}

theorem sq_expt (T : GrpData p q) {Y : Mat p q} (hY : Y ∈ upq p q) :
    ((T.sq (T.expt Y) : ℂˣ) : ℂ) = Complex.exp (Y.trace / 2) := by
  have h1 := T.expt_add Y hY (1 / 2) (1 / 2)
  rw [add_halves, one_smul] at h1
  rw [h1, map_mul, Units.val_mul, ← sq, T.sq_sq, T.expt_cov _ (KStabLie.smul_mem_upq hY _),
    GlobalTheory.DetSqrtCover.det_exp, Matrix.trace_smul]
  congr 1
  simp [div_eq_inv_mul]

theorem matG_mul_inv (T : GrpData p q) (g : T.G) : matG T g * matG T g⁻¹ = 1 := by
  rw [← matG_mul, mul_inv_cancel, matG_one]

theorem matG_inv_mul (T : GrpData p q) (g : T.G) : matG T g⁻¹ * matG T g = 1 := by
  rw [← matG_mul, inv_mul_cancel, matG_one]

theorem conj_mem_upq (T : GrpData p q) (g : T.G) {Y : Mat p q} (hY : Y ∈ upq p q) :
    matG T g * Y * matG T g⁻¹ ∈ upq p q := by
  have h : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  have h1 := matG_J T g
  have h2 : (matG T g)ᴴ * Jm p q = Jm p q * matG T g⁻¹ := by
    conv_rhs => rw [← h1]
    rw [Matrix.mul_assoc _ (matG T g), matG_mul_inv, Matrix.mul_one]
  have h3 : Jm p q * matG T g = (matG T g⁻¹)ᴴ * Jm p q := by
    conv_lhs => rw [← matG_J T g⁻¹]
    rw [Matrix.mul_assoc _ _ (matG T g), matG_inv_mul, Matrix.mul_one]
  change _ + _ = 0
  calc _ = (matG T g⁻¹)ᴴ * (Yᴴ * ((matG T g)ᴴ * Jm p q)) + (Jm p q * matG T g) * Y * matG T g⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (matG T g⁻¹)ᴴ * (Yᴴ * Jm p q + Jm p q * Y) * matG T g⁻¹ := by
        rw [h2, h3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h]; simp

theorem expt_conj (T : GrpData p q) (g : T.G) {Y : Mat p q} (hY : Y ∈ upq p q) :
    T.expt (matG T g * Y * matG T g⁻¹) * g = g * T.expt Y := by
  apply T.emb.injective
  simp only [map_mul, Prod.mk.injEq]
  constructor
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, T.expt_cov _ (conj_mem_upq T g hY), T.expt_cov _ hY, matG_inv, matG,
      Matrix.exp_units_conj, Units.inv_mul_cancel_right]
  · rw [mul_comm]
    congr 1
    apply Units.ext
    rw [sq_expt T hY, sq_expt T (conj_mem_upq T g hY), Matrix.trace_mul_cycle, matG_inv_mul, Matrix.one_mul]

def kronOne (p q r s : ℕ) : Mat p q →+* Mat (p * r + q * s) (p * s + q * r) where
  toFun Y := Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s))
  map_one' := by simp
  map_mul' X Y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := by simp
  map_add' X Y := by
    ext; simp [add_mul]

theorem kronOne_apply (Y : Mat p q) : kronOne p q r s Y =
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s)) := rfl

theorem kronOne_smul (t : ℝ) (Y : Mat p q) : kronOne p q r s (t • Y) = t • kronOne p q r s Y := by
  ext; simp [kronOne_apply, mul_assoc]

theorem kronOne_exp (Y : Mat p q) :
    kronOne p q r s (NormedSpace.exp Y) = NormedSpace.exp (kronOne p q r s Y) := by
  have hc : Continuous (kronOne p q r s) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [kronOne_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (kronOne p q r s) hc Y

def sgnIx : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem mem_upq_iff (Y : Mat p q) : Y ∈ upq p q ↔ ∀ a b, star (Y b a) * sgnIx b + sgnIx a * Y a b = 0 := by
  change Yᴴ * Jm p q + Jm p q * Y = 0 ↔ _
  rw [KStabLie.Jm_eq, ← Matrix.ext_iff]
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, sgnIx]

theorem sgnIx_lineEquiv (l : Ln p q r s) : sgnIx (lineEquiv p q r s l) = sgnIx l.1 * sgnIx l.2 := by
  have h := lineEquiv_isLeft l
  rcases hl : lineEquiv p q r s l with x | x <;> rw [hl] at h <;>
    rcases l with ⟨a | a, c | c⟩ <;> simp [linePos] at h <;> simp [sgnIx]

theorem kronOne_mem {Y : Mat p q} (hY : Y ∈ upq p q) :
    kronOne p q r s Y ∈ upq (p * r + q * s) (p * s + q * r) := by
  rw [mem_upq_iff] at hY ⊢
  intro a b
  obtain ⟨⟨a, c⟩, rfl⟩ := (lineEquiv p q r s).surjective a
  obtain ⟨⟨b, d⟩, rfl⟩ := (lineEquiv p q r s).surjective b
  simp only [kronOne_apply, sgnIx_lineEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h : c = d
  · subst h
    simp only [if_true, mul_one]
    linear_combination sgnIx c * hY a b
  · simp [h, Ne.symm h]

theorem trace_kronOne (Y : Mat p q) : (kronOne p q r s Y).trace = ((r + s : ℕ) : ℂ) * Y.trace := by
  have : (kronOne p q r s Y).trace = (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s)).trace := by
    simp only [Matrix.trace, Matrix.diag, kronOne_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact (lineEquiv p q r s).symm.sum_comp fun l => Matrix.kroneckerMap (· * ·) Y (1 : Mat r s) l l
  rw [this, Matrix.trace_kronecker, Matrix.trace_one, mul_comm]
  simp

variable {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

theorem emb_expt (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) :
    F.emb (T1.expt Y, 1) = T0.expt (kronOne p q r s Y) := by
  apply T0.emb.injective
  simp only [Prod.mk.injEq]
  constructor
  · apply Units.ext
    rw [F.emb_cov, T0.expt_cov _ (kronOne_mem hY), T1.expt_cov _ hY, map_one, Units.val_one, ← kronOne_exp]
    rfl
  · apply Units.ext
    rw [F.emb_sq, map_one, one_pow, mul_one, Units.val_pow_eq_pow_val, sq_expt T1 hY, sq_expt T0 (kronOne_mem hY),
      trace_kronOne, ← Complex.exp_nat_mul, mul_div_assoc]

theorem hasDerivAt_pi (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (P : Pol p q r s) :
    HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0 := by
  have h := F.der _ (kronOne_mem (r := r) (s := s) hY) P
  have hact : omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (kronOne p q r s Y)) = fockAct1 p q r s Y := by
    rw [kronOne_apply, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    rfl
  rw [hact] at h
  convert h using 2 with t
  rw [← kronOne_smul, ← emb_expt F (KStabLie.smul_mem_upq hY t)]
  rfl

theorem pi_mul (F : FockData T0 T1 T2) (g h : T1.G) (x : F.H) :
    F.π (g * h, 1) x = F.π (g, 1) (F.π (h, 1) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem pi_one (F : FockData T0 T1 T2) (x : F.H) : F.π (1, 1) x = x := by
  rw [Prod.mk_one_one, map_one, ContinuousLinearMap.one_apply]

theorem norm_pi (F : FockData T0 T1 T2) (g : T1.G) (x : F.H) : ‖F.π (g, 1) x‖ = ‖x‖ := F.isom _ x

theorem inner_pi (F : FockData T0 T1 T2) (g : T1.G) (x y : F.H) :
    inner ℂ (F.π (g, 1) x) (F.π (g, 1) y) = inner ℂ x y :=
  LinearIsometry.inner_map_map (⟨(F.π (g, 1)).toLinearMap, norm_pi F g⟩ : F.H →ₗᵢ[ℂ] F.H) x y

theorem hasDerivAt_pi_at (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (P : Pol p q r s) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P))
      (F.π (T1.expt (t • Y), 1) (F.ι (fockAct1 p q r s Y P))) t := by
  have h1 := ((F.π (T1.expt (t • Y), 1)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_pi F hY P)
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
  convert h2 using 2 with u
  · simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← pi_mul, ← T1.expt_add Y hY, add_sub_cancel]
  · rfl

theorem covariance_real (F : FockData T0 T1 T2) (g : T1.G) {Y : Mat p q} (hY : Y ∈ upq p q)
    (P Q : Pol p q r s) :
    inner ℂ (F.ι Q) (F.π (g, 1) (F.ι (fockAct1 p q r s Y P))) =
      -inner ℂ (F.ι (fockAct1 p q r s (matG T1 g * Y * matG T1 g⁻¹) Q)) (F.π (g, 1) (F.ι P)) := by
  set Z := matG T1 g * Y * matG T1 g⁻¹ with hZd
  have hZ : Z ∈ upq p q := conj_mem_upq T1 g hY
  have h1 := ((F.π (g, 1)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi F hY P)
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_pi F hZ Q) h1
  have h3 : (fun t : ℝ => inner ℂ (F.π (T1.expt (t • Z), 1) (F.ι Q))
      ((⇑((F.π (g, 1)).restrictScalars ℝ) ∘ fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) t)) =
      fun _ => inner ℂ (F.ι Q) (F.π (g, 1) (F.ι P)) := by
    funext t
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← pi_mul, ← expt_conj T1 g (KStabLie.smul_mem_upq hY t), pi_mul, Matrix.mul_smul, Matrix.smul_mul,
      inner_pi]
  rw [h3] at h2
  have h4 := h2.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', zero_smul, T1.expt_zero,
    pi_one] at h4
  linear_combination h4

theorem adjZ_of_mem {Y : Mat p q} (hY : Y ∈ upq p q) : adjZ Y = -Y := by
  have h : Yᴴ * Jm p q = -(Jm p q * Y) := eq_neg_of_add_eq_zero_left hY
  rw [adjZ, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, KStabLie.Jm_sq, Matrix.one_mul]

open DerivedAdjoint in

theorem covariance (F : FockData T0 T1 T2) (g : T1.G) (Z : Mat p q) (P Q : Pol p q r s) :
    inner ℂ (F.ι Q) (F.π (g, 1) (F.ι (fockAct1 p q r s Z P))) =
      inner ℂ (F.ι (fockAct1 p q r s (adjZ (matG T1 g * Z * matG T1 g⁻¹)) Q)) (F.π (g, 1) (F.ι P)) := by
  obtain ⟨X, Y, hX, hY, rfl⟩ : ∃ X Y : Mat p q, adjZ X = -X ∧ adjZ Y = -Y ∧
      Z = X + Complex.I • Y := by
    refine ⟨(1 / 2 : ℂ) • (Z - adjZ Z), (-Complex.I / 2) • (Z + adjZ Z), ?_, ?_, ?_⟩
    · rw [adjZ_smul, adjZ_sub, adjZ_adjZ, show star (1 / 2 : ℂ) = 1 / 2 by simp]
      module
    · rw [adjZ_smul, adjZ_add, adjZ_adjZ, show star (-Complex.I / 2) = Complex.I / 2 by simp]
      module
    · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
      module
  have hX' := mem_upq_of_adjZ hX
  have hY' := mem_upq_of_adjZ hY
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, adjZ_add, adjZ_smul,
    adjZ_of_mem (conj_mem_upq T1 g hX'), adjZ_of_mem (conj_mem_upq T1 g hY')]
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_neg_left, covariance_real F g hX', covariance_real F g hY']
  simp

end GlobalTheory.FockDecay
end

noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.FockAlg GlobalTheory.RealPar GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues Matrix

variable {p q n : ℕ} {T0 : GrpData (p * n + q * 0) (p * 0 + q * n)} {T1 : GrpData p q} {T2 : GrpData n 0}

theorem act_lower {Φ : Pol p q n 0} (h : KilledByPMinus Φ) (C : Matrix (Fin q) (Fin p) ℂ) :
    fockAct1 p q n 0 (Matrix.fromBlocks 0 0 C 0) Φ = 0 := by
  have e : (Matrix.fromBlocks 0 0 C 0 : Mat p q) = ∑ b, ∑ a, C b a • Eab (Sum.inr b) (Sum.inl a) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Eab, Matrix.sum_apply, Matrix.single_apply, ite_and]
  rw [e]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fockAct1_lower, h _ _, neg_zero,
    smul_zero, Finset.sum_const_zero]

theorem adjZ_upper (B : Matrix (Fin p) (Fin q) ℂ) :
    adjZ (Matrix.fromBlocks 0 B 0 0 : Mat p q) = Matrix.fromBlocks 0 0 (-Bᴴ) 0 := by
  simp [adjZ, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem exists_killed (F : FockData T0 T1 T2) {k : T1.G} (hk : k ∈ T1.Kset) {Φ : Pol p q n 0}
    (h : KilledByPMinus Φ) : ∃ Q, F.π (k, 1) (F.ι Φ) = F.ι Q ∧ KilledByPMinus Q := by
  have hQ : F.π (k, 1) (F.ι Φ) ∈ LinearMap.range F.ι := by
    rw [← MvPolynomial.sum_homogeneousComponent Φ, map_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    obtain ⟨Q, -, e⟩ := GlobalTheory.FockDegree.Om_Kset_homog p q n 0 T0 T1 T2 F _
      (GlobalTheory.FockKFin.emb_mem_Kset F hk (GlobalTheory.FockKFin.one_mem_Kset T2)) d _
      (MvPolynomial.homogeneousComponent_mem d Φ)
    exact ⟨Q, e.symm⟩
  obtain ⟨Q, hQ⟩ := hQ
  refine ⟨Q, hQ.symm, fun a b => ?_⟩
  set E : Mat p q := Eab (Sum.inr b) (Sum.inl a) with hE
  have hE' : E = Matrix.fromBlocks 0 0 (Matrix.single b a 1) 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [hE, Eab, Matrix.single_apply]
  obtain ⟨U, -, V, -, h1⟩ := exists_blocks T1 hk
  obtain ⟨U', -, V', -, h2⟩ := exists_blocks T1 ((Ksub T1).inv_mem hk)
  have h3 : fockAct1 p q n 0 (matG T1 k⁻¹ * E * matG T1 k) Φ = 0 := by
    rw [h1, h2, hE']
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact act_lower h _
  have h4 := covariance F k (matG T1 k⁻¹ * E * matG T1 k) Φ (fockAct1 p q n 0 E Q)
  have h5 := covariance F 1 E Q (fockAct1 p q n 0 E Q)
  have h6 : matG T1 k * (matG T1 k⁻¹ * E * matG T1 k) * matG T1 k⁻¹ = E := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, matG_mul_inv, Matrix.one_mul, Matrix.mul_assoc, matG_mul_inv,
      Matrix.mul_one]
  rw [h3, map_zero, map_zero, inner_zero_right, h6, ← hQ] at h4
  rw [inv_one, matG_one, Matrix.one_mul, Matrix.mul_one, pi_one, pi_one, ← h4, inner_self_eq_zero] at h5
  have h7 := F.ι_inj (h5.trans (map_zero _).symm)
  rwa [hE, fockAct1_lower, neg_eq_zero] at h7

theorem act_tanhDiag (σ : ℕ → ℝ) (t : ℝ) (α : Ln p q n 0 →₀ ℕ) :
    fockAct1 p q n 0 (tanhDiag p q σ t) (MvPolynomial.monomial α 1) =
      ((∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * (σ (posIx l.1) * Real.tanh (t * σ (posIx l.1))) : ℝ) : ℂ) •
        MvPolynomial.monomial α 1 := by
  have e : tanhDiag p q σ t = ∑ a : Ix p q, ((if a.isLeft then 1 else -1) *
      ((σ (posIx a) * Real.tanh (t * σ (posIx a)) : ℝ) : ℂ)) • Eab a a := by
    ext i j
    simp only [tanhDiag, Eab, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply,
      ite_and, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [e, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, cartan1, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Complex.ofReal_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rcases c with c | c
  · rcases a with a | a <;> simp [lineSign] <;> ring
  · exact c.elim0

def logCosh (σ : ℕ → ℝ) (t : ℝ) (a : Ix p q) : ℝ := Real.log (Real.cosh (t * σ (posIx a)))

theorem hasDerivAt_logCosh (σ : ℕ → ℝ) (t : ℝ) (a : Ix p q) :
    HasDerivAt (fun t => logCosh σ t a) (σ (posIx a) * Real.tanh (t * σ (posIx a))) t := by
  have h := ((hasDerivAt_id t).mul_const (σ (posIx a))).cosh.log (Real.cosh_pos _).ne'
  refine h.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [id]
  ring

theorem dil_eq_sum (u : Ix p q → ℝ) (Ψ : Pol p q n 0) :
    dil n u Ψ = ∑ α ∈ Ψ.support, (Ψ.coeff α *
      ((Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) : ℝ) : ℂ)) • MvPolynomial.monomial α 1 := by
  conv_lhs => rw [Ψ.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [dil_monomial, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial]
  simp [mul_comm]

theorem hasDerivAt_flow (F : FockData T0 T1 T2) (σ : ℕ → ℝ) (Ψ : Pol p q n 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F.π (T1.expt (t • diagP p q σ), 1) (F.ι (dil n (logCosh σ t) Ψ)))
      (F.π (T1.expt (t • diagP p q σ), 1)
        (F.ι (fockAct1 p q n 0 (diagP p q σ + tanhDiag p q σ t) (dil n (logCosh σ t) Ψ)))) t := by
  simp only [dil_eq_sum, map_sum, map_smul]
  refine HasDerivAt.fun_sum fun α _ => ?_
  have h1 : HasDerivAt (fun t : ℝ => ∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * logCosh σ t l.1)
      (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * (σ (posIx l.1) * Real.tanh (t * σ (posIx l.1)))) t :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_logCosh σ t l.1).const_mul _
  have h2 := (h1.exp.ofReal_comp.const_mul (Ψ.coeff α)).fun_smul
    (hasDerivAt_pi_at F (diagonalElement_mem p q σ).1 (MvPolynomial.monomial α 1) t)
  refine h2.congr_deriv ?_
  rw [map_add, LinearMap.add_apply, act_tanhDiag, map_add, map_add, map_smul, map_smul, smul_add, smul_smul,
    Complex.ofReal_mul, mul_assoc]

theorem inner_flow (F : FockData T0 T1 T2) (σ : ℕ → ℝ) (hσ : ∀ i, min p q ≤ i → σ i = 0)
    {Ψ Φ : Pol p q n 0} (hΨ : KilledByPMinus Ψ) (hΦ : KilledByPMinus Φ) :
    inner ℂ (F.ι Φ) (F.π (T1.expt (diagP p q σ), 1) (F.ι (dil n (logCosh σ 1) Ψ))) =
      inner ℂ (F.ι Φ) (F.ι Ψ) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => inner ℂ (F.ι Φ)
      (F.π (T1.expt (t • diagP p q σ), 1) (F.ι (dil n (logCosh σ t) Ψ)))) 0 t := by
    intro t
    refine (HasDerivAt.inner ℂ (hasDerivAt_const t (F.ι Φ)) (hasDerivAt_flow F σ Ψ t)).congr_deriv ?_
    obtain ⟨B, C, h⟩ := exists_gauss σ hσ t
    have hg : matG T1 (T1.expt (t • diagP p q σ)) = hypMat p q σ t := by
      rw [← exp_diagP σ hσ t]
      exact T1.expt_cov _ (KStabLie.smul_mem_upq (diagonalElement_mem p q σ).1 t)
    have h1 := covariance F (T1.expt (t • diagP p q σ))
      (diagP p q σ + tanhDiag p q σ t - Matrix.fromBlocks 0 0 C 0) (dil n (logCosh σ t) Ψ) Φ
    rw [← hg] at h
    rw [h, Matrix.mul_assoc, matG_mul_inv, Matrix.mul_one, adjZ_upper, act_lower hΦ, map_zero, inner_zero_left,
      map_sub, LinearMap.sub_apply, act_lower (killed_dil _ hΨ), sub_zero] at h1
    rw [h1, inner_zero_left, add_zero]
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  have h0 : (logCosh σ 0 : Ix p q → ℝ) = 0 := by
    funext a; simp [logCosh]
  simpa only [one_smul, zero_smul, T1.expt_zero, pi_one, h0, dil_zero] using h

theorem harmonicDecay : HarmonicDecay := by
  intro p q n T0 T1 T2 F X hX Φ₁ Φ₂ h₁ h₂
  obtain ⟨σ, hσ, hs, k, hk, hXk⟩ := exists_conj_diagP T1 hX
  have hk' : k⁻¹ ∈ T1.Kset := (Ksub T1).inv_mem hk
  obtain ⟨Q₁, e₁, k₁⟩ := exists_killed F hk' h₁
  obtain ⟨Q₂, e₂, k₂⟩ := exists_killed F hk' h₂
  have hX' : matG T1 k * diagP p q σ * matG T1 k⁻¹ = X := by
    rw [← hXk, Matrix.mul_assoc, matG_mul_inv, Matrix.mul_one]
  have hg : k⁻¹ * T1.expt X = T1.expt (diagP p q σ) * k⁻¹ := by
    have := expt_conj T1 k (diagonalElement_mem p q σ).1
    rw [hX'] at this
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← this, mul_inv_cancel_right]
  have hc : coef F X Φ₁ Φ₂ = inner ℂ (F.ι Q₂) (F.ι (dil n (-logCosh σ 1) Q₁)) := by
    rw [coef, ← inner_pi F k⁻¹, ← pi_mul, hg, pi_mul, e₁, e₂,
      ← inner_flow F σ hσ (killed_dil _ k₁) k₂, dil_dil_neg]
  have hn := norm_dil_le (isFockIsometry_of_fockData F) (logCosh σ 1)
    (fun a => Real.log_nonneg (Real.one_le_cosh _)) Q₁
  have hp := exp_sum_logCosh (n := n) σ hσ
  simp only [logCosh, one_mul] at hn
  rw [hp, ← e₁, norm_pi] at hn
  simp only [hs] at hn
  rw [hc, mul_comm]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [← e₂, norm_pi]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)

end GlobalTheory.FockDecay
end

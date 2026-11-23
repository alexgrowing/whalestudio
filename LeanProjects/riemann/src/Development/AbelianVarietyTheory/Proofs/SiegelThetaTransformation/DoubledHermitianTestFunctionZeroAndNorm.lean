import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TestFunctionWitness
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpecStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenbergStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblZero

section Ip

variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
  {φ φ' ψ ψ' : Matrix κ ι K → ℂ}

theorem ip_self_pos (h : IsSB φ) (h0 : φ ≠ 0) : ∃ t : ℝ, 0 < t ∧ ip φ φ = t := by
  obtain ⟨R, hR, h⟩ := h
  obtain ⟨h1, h2, h3, -⟩ := ip_self_nonneg_and_bounds K κ ι R φ hR h
  refine ⟨(ip φ φ).re, lt_of_le_of_ne h2 fun e => h0 (funext fun x => ?_), ?_⟩
  · have := h3 x
    rw [← e, mul_zero] at this
    simpa using le_antisymm this (sq_nonneg _)
  · exact Complex.ext (by simp) (by simpa using h1)

theorem ip_self_ne_zero (h : IsSB φ) (h0 : φ ≠ 0) : ip φ φ ≠ 0 := by
  obtain ⟨t, ht, e⟩ := ip_self_pos h h0
  rw [e]; exact_mod_cast ht.ne'

theorem isSB_mul_conj (h : IsSB φ) (h' : IsSB ψ) : IsSB fun x => φ x * conj (ψ x) :=
  (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ h (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ h' h').2.2.2.1).2.2.1

theorem ip_add_left (h : IsSB φ) (h' : IsSB φ') (k : IsSB ψ) :
    ip (φ + φ') ψ = ip φ ψ + ip φ' ψ := by
  rw [ip, ip, ip, ← (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ (isSB_mul_conj h k) (isSB_mul_conj h' k)).2.2.2.2.1]
  congr 1; funext x; simp [add_mul]

theorem ip_add_right (h : IsSB φ) (k : IsSB ψ) (k' : IsSB ψ') :
    ip φ (ψ + ψ') = ip φ ψ + ip φ ψ' := by
  rw [ip, ip, ip, ← (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ (isSB_mul_conj h k) (isSB_mul_conj h k')).2.2.2.2.1]
  congr 1; funext x; simp [mul_add]

theorem ip_smul (h : IsSB φ) (k : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  rw [ip, ip, ← (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ (isSB_mul_conj h k) (isSB_mul_conj h k)).2.2.2.2.2.1]
  congr 1; funext x; simp; ring

end Ip

section Schur

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

noncomputable def cosetInd (R : ℕ) (q : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) : Matrix κ ι ℚ → ℂ :=
  fun x => if (x : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) = q then 1 else 0

omit [DecidableEq ι] [Fintype κ] [Fintype ι] in

theorem hasLevel_cosetInd_zero (R : ℕ) : HasLevel R (cosetInd (κ := κ) (ι := ι) R 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have h : (x : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) = 0 := by
      by_contra h; exact hx (if_neg h)
    obtain ⟨y, hy, rfl⟩ := IpPos.exists_of_mem_perSub ((QuotientAddGroup.eq_zero_iff _).1 h)
    exact IpPos.intM_natCast_smul _ (IpPos.intM_natCast_smul _ hy)
  · have h : (((R : ℚ) • y : Matrix κ ι ℚ) : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure ⟨y, hy, rfl⟩)
    simp only [cosetInd, QuotientAddGroup.mk_add, h, add_zero]

omit [DecidableEq ι] in

theorem heisS_cosetInd_zero (R : ℕ) (q : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) :
    heisS 0 q.out (cosetInd R 0) = cosetInd R q := by
  funext x
  have h : ∀ k, (0 : Matrix κ ι ℚ) k = 0 := fun _ => rfl
  simp [heisS, cosetInd, h, sub_eq_zero]

theorem isSB_cosetInd {R : ℕ} (hR : 0 < R) (q : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) :
    IsSB (cosetInd R q) := by
  rw [← heisS_cosetInd_zero]
  exact (GlobalTheory.T.heisenbergOperatorRationalPoint_laws _ _ _ _ _ ⟨R, hR, hasLevel_cosetInd_zero R⟩).1

theorem heisS_cosetInd_char {R : ℕ} (hR : 0 < R) (q : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) (k : κ) (i : ι) :
    heisS (Matrix.single k i (R : ℚ)⁻¹) 0 (cosetInd R q) =
      cexp (2 * π * I * ((q.out k i / R : ℚ) : ℂ)) • cosetInd R q := by
  funext x
  have h : ∀ k, (0 : Matrix κ ι ℚ) k = 0 := fun _ => rfl
  have hs : (∑ k', (2 * (x k' ⬝ᵥ Matrix.single k i (R : ℚ)⁻¹ k') -
      Matrix.single k i (R : ℚ)⁻¹ k' ⬝ᵥ (0 : Matrix κ ι ℚ) k') : ℚ) = 2 * (x k i / R) := by
    simp [h, dotProduct, Matrix.single, ite_and, div_eq_mul_inv, ← Finset.mul_sum]
  rw [heisS, hs, sub_zero, Pi.smul_apply, smul_eq_mul, mul_comm]
  by_cases hx : (x : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) = q
  · congr 1
    have h1 : ((q.out : Matrix κ ι ℚ) : Matrix κ ι ℚ ⧸ perSub ℚ κ ι R) = x := by
      rw [QuotientAddGroup.out_eq', hx]
    obtain ⟨y, hy, e⟩ := IpPos.exists_of_mem_perSub (QuotientAddGroup.eq.1 h1)
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hy k i)
    have e1 := congrFun (congrFun e k) i
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, ← hm,
      algebraMap_int_eq, eq_intCast] at e1
    have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
    have e2 : x k i / R = q.out k i / R + m := by
      field_simp; linear_combination e1
    rw [e2, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m, by push_cast; ring⟩
  · simp [cosetInd, hx]

omit [DecidableEq ι] in

theorem eq_sum_cosetInd {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ} (hφ : HasLevel R φ) :
    φ = ∑ q ∈ (IpPos.classes_finite_card (K := ℚ) (κ := κ) (ι := ι) hR).1.toFinset,
      φ q.out • cosetInd R q := by
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, cosetInd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · exact (IpPos.apply_out_mk hφ x).symm
  · by_contra hx
    refine h ?_
    rw [Set.Finite.mem_toFinset]
    exact hφ.1 _ (by rwa [IpPos.apply_out_mk hφ x])

omit [DecidableEq ι] in

theorem map_sum_of_isSB {α : Type} (m : (Matrix κ ι ℚ → ℂ) → ℂ) (h0 : m 0 = 0)
    (hadd : ∀ φ ψ, IsSB φ → IsSB ψ → m (φ + ψ) = m φ + m ψ) (f : α → Matrix κ ι ℚ → ℂ)
    (hf : ∀ a, IsSB (f a)) (s : Finset α) :
    IsSB (∑ a ∈ s, f a) ∧ m (∑ a ∈ s, f a) = ∑ a ∈ s, m (f a) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using isSB_zero, by simpa using h0⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (hf a) ih.1, ih.2]
    exact ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ (hf a) ih.1).1, rfl⟩

theorem exists_eq_mul_ip (l : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ) → ℂ)
    (h1 : ∀ φ φ' ψ, IsSB φ → IsSB φ' → IsSB ψ → l (φ + φ') ψ = l φ ψ + l φ' ψ)
    (h2 : ∀ φ ψ ψ', IsSB φ → IsSB ψ → IsSB ψ' → l φ (ψ + ψ') = l φ ψ + l φ ψ')
    (hs : ∀ (a b : ℂ) φ ψ, IsSB φ → IsSB ψ → l (a • φ) (b • ψ) = a * conj b * l φ ψ)
    (hi : ∀ a b φ ψ, IsSB φ → IsSB ψ → l (heisS a b φ) (heisS a b ψ) = l φ ψ) :
    ∃ c : ℂ, ∀ φ ψ, IsSB φ → IsSB ψ → l φ ψ = c * ip φ ψ := by
  have sm : ∀ (c : ℂ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (c • φ) := fun c φ h =>
    (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ h h).2.1 c
  have lev : ∀ R : ℕ, 0 < R → ∃ c : ℂ, ∀ φ ψ, HasLevel R φ → HasLevel R ψ →
      l φ ψ = c * ip φ ψ := by
    intro R hR
    have hRQ : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
    have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have sb := isSB_cosetInd (κ := κ) (ι := ι) hR
    have diag : ∀ q, l (cosetInd R q) (cosetInd R q) = l (cosetInd R 0) (cosetInd R 0) := by
      intro q
      rw [← heisS_cosetInd_zero, hi _ _ _ _ (sb 0) (sb 0)]
    have off : ∀ q q', q ≠ q' → l (cosetInd R q) (cosetInd R q') = 0 := by
      intro q q' hne
      by_contra h0
      apply hne
      have key : ∀ k i, IsIntegral ℤ ((R : ℚ)⁻¹ * (-q'.out + q.out) k i) := by
        intro k i
        have := hi (Matrix.single k i (R : ℚ)⁻¹) 0 _ _ (sb q) (sb q')
        rw [heisS_cosetInd_char hR, heisS_cosetInd_char hR, hs _ _ _ _ (sb q) (sb q'),
          mul_eq_right₀ h0, ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_eq_one_iff] at this
        obtain ⟨m, hm⟩ := this
        simp only [map_mul, map_ofNat, conj_ofReal, conj_I, map_ratCast] at hm
        have e : (((R : ℚ)⁻¹ * (-q'.out + q.out) k i : ℚ) : ℂ) = ((m : ℚ) : ℂ) := by
          apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
          simp only [Matrix.add_apply, Matrix.neg_apply]
          push_cast at hm ⊢
          linear_combination hm
        rw [Rat.cast_injective e]
        exact isIntegral_algebraMap (R := ℤ) (x := m)
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      symm
      apply QuotientAddGroup.eq.2
      refine AddSubgroup.subset_closure ⟨(R : ℚ)⁻¹ • (-q'.out + q.out), key, ?_⟩
      rw [smul_inv_smul₀ hRQ]
    refine ⟨l (cosetInd R 0) (cosetInd R 0) *
      (R : ℂ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)), fun φ ψ hφ hψ => ?_⟩
    have z1 : ∀ ψ, IsSB ψ → l 0 ψ = 0 := fun ψ h => by
      simpa using hs 0 1 0 ψ isSB_zero h
    have z2 : ∀ ψ, IsSB ψ → l ψ 0 = 0 := fun ψ h => by
      simpa using hs 1 0 ψ 0 h isSB_zero
    rw [IpPos.ip_eq_sum hR hφ hψ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hRC),
      Finset.mul_sum]
    conv_lhs => rw [eq_sum_cosetInd hR hφ]
    rw [(map_sum_of_isSB (fun φ => l φ ψ) (z1 _ ⟨R, hR, hψ⟩)
      (fun _ _ a b => h1 _ _ _ a b ⟨R, hR, hψ⟩) _ (fun q => sm _ _ (sb q)) _).2]
    refine Finset.sum_congr rfl fun q hq => ?_
    conv_lhs => rw [eq_sum_cosetInd hR hψ]
    rw [(map_sum_of_isSB (l _) (z2 _ (sm _ _ (sb q)))
      (fun _ _ a b => h2 _ _ _ (sm _ _ (sb q)) a b) _ (fun q => sm _ _ (sb q)) _).2,
      Finset.sum_eq_single_of_mem q hq, hs _ _ _ _ (sb q) (sb q), diag, mul_comm]
    intro q' _ hne
    rw [hs _ _ _ _ (sb q) (sb q'), off _ _ hne.symm, mul_zero]
  obtain ⟨c, hc⟩ := lev 1 one_pos
  refine ⟨c, ?_⟩
  rintro φ ψ ⟨R, hR, hφ⟩ ⟨S, hS, hψ⟩
  obtain ⟨c', hc'⟩ := lev (R * S) (Nat.mul_pos hR hS)
  have hl : HasLevel (R * S) (fun x : Matrix κ ι ℚ => if IntM x then (1 : ℂ) else 0) := by
    simpa using IpPos.hasLevel_mul (ind_sb (K := ℚ) (κ := κ) (ι := ι)) (R * S)
  have e := (hc' _ _ hl hl).symm.trans (hc _ _ ind_sb ind_sb)
  rw [mul_left_inj' (ip_self_ne_zero ind_isSB ind_ne_zero)] at e
  rw [← e]
  exact hc' _ _ (IpPos.hasLevel_mul hφ S) (mul_comm S R ▸ IpPos.hasLevel_mul hψ R)

end Schur

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem ip_heisH (d b : Matrix (Fin n) (Fin r) E) {φ ψ : Matrix (Fin n) (Fin r) E → ℂ}
    (h : IsSB φ) (k : IsSB ψ) : ip (heisH d b φ) (heisH d b ψ) = ip φ ψ := by
  rw [ip, ip, ← ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ (isSB_mul_conj h k) (isSB_mul_conj h k)).2.2.2.2.2.2.2 d).2]
  congr 1; funext x
  have e : ∀ t : ℚ, cexp (π * I * t) * conj (cexp (π * I * t)) = 1 := fun t => by
    rw [← Complex.exp_conj, ← Complex.exp_add]; simp
  simp only [heisH, map_mul]
  rw [mul_mul_mul_comm, e, mul_one]

theorem exists_heisG (hs : IsSympl X bas) (a b : Matrix (Fin n) (Fin g) ℚ) :
    ∃ y : Matrix (Fin n) (Fin r) E, ∀ φ, heisG X bas y φ = heisS a b φ :=
  ⟨fun k => vecQ X bas (Sum.elim (a k) (b k)), fun φ => by
    simp only [heisG, crd_vecQ hs]; rfl⟩

theorem toCols₁_dblT (y₁ y₂ : Matrix (Fin n) (Fin r) E) :
    (Matrix.fromCols y₁ y₂ * dblT X).toCols₁ = y₁ - y₂ := by
  rw [dblT, Matrix.fromCols_mul_fromBlocks, Matrix.toCols₁_fromCols]
  simp [sub_eq_add_neg]

theorem dom_nonempty (X : Data E r) : X.dom.Nonempty := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem dbl_self_ne_zero (hs : IsSympl X bas) (hn : Even n) {φ : TF n g} (h : IsSB φ)
    (h0 : φ ≠ 0) : dbl X bas idx φ φ ≠ 0 := by
  intro e
  obtain ⟨x, hx⟩ := dom_nonempty X
  have hd := (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hs hn φ φ h h).2.1 x hx x hx
  refine h0 (eq_of_thS_eq _ _ φ 0 h isSB_zero _
    ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩ fun ζ => ?_)
  have h1 := hd (fun k => perMat X bas idx Sum.inl x *ᵥ ζ k)
    (fun k i => conj ((perMat X bas idx Sum.inl x *ᵥ ζ k) i))
  simp only [Complex.conj_conj, e, thH, Pi.zero_apply, zero_mul, tsum_zero, mul_zero,
    mul_eq_zero, map_eq_zero, or_self] at h1
  have hdet : (hMat X bas idx x).det ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (hMat_mul_perMat idx hs hx)).ne_zero
  simp only [thA, mulVec_mulVec, hMat_mul_perMat idx hs hx, one_mulVec, mul_eq_zero,
    Complex.exp_ne_zero, pow_ne_zero _ hdet, false_or] at h1
  rw [show thS φ _ ζ = 0 from h1]
  simp [thS]

end Main

end GlobalTheory.SW.DblZero

open GlobalTheory.SW.DblZero in

theorem GlobalTheory.SW.dbl_zero_and_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∃ a : ℂ, a ≠ 0 ∧ ∃ b : ℝ, 0 < b ∧ ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → dbl X bas idx φ₁ φ₂ 0 = a * ip φ₁ φ₂ ∧ ip (dbl X bas idx φ₁ φ₂) (dbl X bas idx φ₁ φ₂) = b * (ip φ₁ φ₁ * ip φ₂ φ₂) := by
  intro E _ _ _ r X g bas idx n hs hn
  have sb := fun φ ψ h k => (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hs hn φ ψ h k).1
  have lin := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn
  have law := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have add1 := fun φ φ' ψ h h' k => ((lin φ ψ h k).1 φ' h').1
  have add2 := fun φ ψ ψ' h k k' => ((lin φ ψ h k).1 ψ' k').2
  have sm1 : ∀ (a : ℂ) φ ψ, IsSB φ → IsSB ψ →
      dbl X bas idx (a • φ) ψ = a • dbl X bas idx φ ψ (n := n) := fun a φ ψ h k => by
    simpa using (lin φ ψ h k).2.1 a 1
  have sm2 : ∀ (a : ℂ) φ ψ, IsSB φ → IsSB ψ →
      dbl X bas idx φ (a • ψ) = conj a • dbl X bas idx φ ψ (n := n) := fun a φ ψ h k => by
    simpa using (lin φ ψ h k).2.1 1 a
  have hl : ∀ y : Matrix (Fin n) (Fin r) E, ∃ b, ∀ φ ψ, IsSB φ → IsSB ψ →
      dbl X bas idx (heisG X bas y φ) ψ = heisH y b (dbl X bas idx φ ψ) := fun y =>
    ⟨_, fun φ ψ h k => by
      have := (lin φ ψ h k).2.2 y 0
      rwa [(law 0 ψ k).2.1, toCols₁_dblT, sub_zero] at this⟩
  have hr : ∀ y : Matrix (Fin n) (Fin r) E, ∃ d b, ∀ φ ψ, IsSB φ → IsSB ψ →
      dbl X bas idx φ (heisG X bas y ψ) = heisH d b (dbl X bas idx φ ψ) := fun y =>
    ⟨_, _, fun φ ψ h k => by
      have := (lin φ ψ h k).2.2 0 y
      rwa [(law 0 φ h).2.1] at this⟩
  obtain ⟨u, hu, hu0⟩ : ∃ u : TF n g, IsSB u ∧ u ≠ 0 := ⟨_, ind_isSB, ind_ne_zero⟩
  have hd0 := dbl_self_ne_zero idx hs hn hu hu0
  obtain ⟨a, ha⟩ := exists_eq_mul_ip (fun φ ψ : TF n g => dbl X bas idx φ ψ 0)
    (fun _ _ _ h h' k => by simp only [add1 _ _ _ h h' k, Pi.add_apply])
    (fun _ _ _ h k k' => by simp only [add2 _ _ _ h k k', Pi.add_apply])
    (fun a b _ _ h k => by simp only [(lin _ _ h k).2.1 a b, Pi.smul_apply, smul_eq_mul])
    (fun a b φ ψ h k => by
      obtain ⟨y, hy⟩ := exists_heisG hs a b
      simp only [← hy, (lin _ _ h k).2.2 y y, toCols₁_dblT, sub_self, heisH]
      simp [cc])
  have first : ∀ ψ ψ' : TF n g, IsSB ψ → IsSB ψ' → ∃ c : ℂ, ∀ φ φ', IsSB φ → IsSB φ' →
      ip (dbl X bas idx φ ψ) (dbl X bas idx φ' ψ') = c * ip φ φ' := fun ψ ψ' k k' =>
    exists_eq_mul_ip (fun φ φ' : TF n g => ip (dbl X bas idx φ ψ) (dbl X bas idx φ' ψ'))
      (fun _ _ _ h h' l => by
        simp only [add1 _ _ _ h h' k, ip_add_left (sb _ _ h k) (sb _ _ h' k) (sb _ _ l k')])
      (fun _ _ _ h l l' => by
        simp only [add1 _ _ _ l l' k', ip_add_right (sb _ _ h k) (sb _ _ l k') (sb _ _ l' k')])
      (fun a b _ _ h l => by
        simp only [sm1 _ _ _ h k, sm1 _ _ _ l k', ip_smul (sb _ _ h k) (sb _ _ l k')])
      (fun a b φ φ' h l => by
        obtain ⟨y, hy⟩ := exists_heisG hs a b
        obtain ⟨b', hb⟩ := hl y
        simp only [← hy, hb _ _ h k, hb _ _ l k', ip_heisH _ _ (sb _ _ h k) (sb _ _ l k')])
  obtain ⟨c, hc⟩ := exists_eq_mul_ip
    (fun ψ' ψ : TF n g => ip (dbl X bas idx u ψ) (dbl X bas idx u ψ'))
    (fun _ _ _ h h' l => by
      simp only [add2 _ _ _ hu h h', ip_add_right (sb _ _ hu l) (sb _ _ hu h) (sb _ _ hu h')])
    (fun _ _ _ h l l' => by
      simp only [add2 _ _ _ hu l l', ip_add_left (sb _ _ hu l) (sb _ _ hu l') (sb _ _ hu h)])
    (fun a b _ _ h l => by
      simp only [sm2 _ _ _ hu h, sm2 _ _ _ hu l, ip_smul (sb _ _ hu l) (sb _ _ hu h),
        Complex.conj_conj, mul_comm a])
    (fun a b φ φ' h l => by
      obtain ⟨y, hy⟩ := exists_heisG hs a b
      obtain ⟨d, b', hb⟩ := hr y
      simp only [← hy, hb _ _ hu h, hb _ _ hu l, ip_heisH _ _ (sb _ _ hu l) (sb _ _ hu h)])
  obtain ⟨t, ht, et⟩ := ip_self_pos hu hu0
  obtain ⟨s, hs0, es⟩ := ip_self_pos (sb _ _ hu hu) hd0
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨a, fun h0 => hd0 (funext fun d => ?_), s / t ^ 2, by positivity, fun φ ψ h k =>
    ⟨ha _ _ h k, ?_⟩⟩
  · obtain ⟨b, hb⟩ := hl (-d)
    have := ha _ _ (law (-d) u hu).1 hu
    simp only [hb _ _ hu hu, h0, zero_mul, heisH, mul_eq_zero, Complex.exp_ne_zero, or_false,
      zero_sub, neg_neg] at this
    exact this
  · obtain ⟨c', hc'⟩ := first ψ ψ k k
    have e1 := hc' u u hu hu
    have e2 := hc ψ ψ k k
    have e3 := hc u u hu hu
    rw [e2, et] at e1
    rw [es, et] at e3
    rw [hc' _ _ h h]
    push_cast
    rw [e3]
    field_simp
    linear_combination (-ip φ φ) * e1

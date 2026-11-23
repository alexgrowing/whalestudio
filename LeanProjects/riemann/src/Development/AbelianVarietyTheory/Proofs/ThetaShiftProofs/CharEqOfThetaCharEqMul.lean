import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEqMulCanonicalThetaOfSignMultiplier
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TwoDvdMultiplierOfThetaZActEqUnitMul

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi thetaChar thetaCharOff omegaStd)
open ReciprocityTheory.PTheta Matrix

namespace ThetaCompare

theorem posSemidef_of_int_nonneg {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 := hp y
    rw [hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
  have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact hq q

variable {g : ℕ}

theorem im_posDef_of_hermForm {M τ : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re)
    (h1 : ∀ j k, (hermForm M (Pi.single j 1) (Pi.single k 1)).im = 0)
    (h2 : ∀ j k, (hermForm M (τ *ᵥ Pi.single j 1) (Pi.single k 1)).im = if j = k then 1 else 0) :
    (τ.map Complex.im).PosDef := by
  have hs : ∀ k : Fin g, star (Pi.single k 1 : Fin g → ℂ) = Pi.single k 1 := fun k => by
    rw [← Pi.single_star, star_one]
  have h1' : ∀ j k, (M j k).im = 0 := fun j k => by simpa [hermForm, hs] using h1 j k
  have hG : (M.map Complex.re).PosDef := by
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext j k
      simpa using congrArg Complex.re (hM.apply j k)
    · have h0 : (fun i => (x i : ℂ)) ≠ 0 := fun h => hx (funext fun i => by simpa using congrFun h i)
      refine (hpos _ h0).trans_eq ?_
      simp [hermForm, dotProduct, mulVec, Complex.re_sum, Complex.im_sum, h1']
  have hY : (τ.map Complex.im)ᵀ * M.map Complex.re = 1 := by
    ext j k
    rw [one_apply, ← h2 j k]
    simp [hermForm, hs, dotProduct, mul_apply, Complex.im_sum, h1']
  have := hG.inv.transpose
  rwa [inv_eq_left_inv hY, transpose_transpose] at this

theorem exists_half_char_of_even {χ : (Fin g → ℤ) → (Fin g → ℤ) → ℂ}
    (hadd : ∀ n m n' m', χ (n + n') (m + m') = χ n m * χ n' m') (h0 : χ 0 0 = 1)
    (hneg : ∀ n m, χ (-n) (-m) = χ n m) :
    ∃ a b : Fin g → ℝ, (∀ k, a k = 0 ∨ a k = 1 / 2) ∧ (∀ k, b k = 0 ∨ b k = 1 / 2) ∧
      ∀ n m, χ n m = eC (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec b ⬝ᵥ ofIntVec n) := by
  have hsgn : ∀ n m, χ n m = 1 ∨ χ n m = -1 := fun n m => by
    refine sq_eq_one_iff.1 ?_
    have := hadd n m (-n) (-m)
    rw [add_neg_cancel, add_neg_cancel, h0, hneg] at this
    rw [sq, ← this]
  obtain ⟨p, q, hpq⟩ := exists_half_char_of_sign hadd hsgn
  have half : ∀ k : ℤ, ((k % 2 : ℤ) : ℝ) / 2 = 0 ∨ ((k % 2 : ℤ) : ℝ) / 2 = 1 / 2 := fun k => by
    rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> simp [hk]
  exact ⟨_, _, fun i => half (p i), fun i => half (q i), fun n m => by rw [hpq, eC_half_char_emod_two]⟩

theorem exists_eq_half {c : Fin g → ℂ} (hc : ∀ k, c k = 0 ∨ c k = 1 / 2) :
    ∃ p : Fin g → ℤ, (∀ k, p k = 0 ∨ p k = 1) ∧ c = fun k => (((p k : ℝ) / 2 : ℝ) : ℂ) := by
  have : ∀ k, ∃ p : ℤ, (p = 0 ∨ p = 1) ∧ c k = (((p : ℝ) / 2 : ℝ) : ℂ) := fun k => by
    rcases hc k with h | h
    · exact ⟨0, Or.inl rfl, by simp [h]⟩
    · exact ⟨1, Or.inr rfl, by simp [h]⟩
  choose p hp hp' using this
  exact ⟨p, hp, funext hp'⟩

theorem char_eq_of_thetaChar_eq_mul {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    {a b a' b' : Fin g → ℂ} (ha : ∀ k, a k = 0 ∨ a k = 1 / 2) (hb : ∀ k, b k = 0 ∨ b k = 1 / 2)
    (ha' : ∀ k, a' k = 0 ∨ a' k = 1 / 2) (hb' : ∀ k, b' k = 0 ∨ b' k = 1 / 2)
    {ρ : (Fin g → ℂ) → ℂ} (hρ : Differentiable ℂ ρ) (hρ0 : ρ 0 ≠ 0)
    (h : ∀ z, thetaChar τ a b z = ρ z * thetaChar τ a' b' z) : a' = a ∧ b' = b := by
  obtain ⟨p, hp, rfl⟩ := exists_eq_half ha
  obtain ⟨q, hq, rfl⟩ := exists_eq_half hb
  obtain ⟨p', hp', rfl⟩ := exists_eq_half ha'
  obtain ⟨q', hq', rfl⟩ := exists_eq_half hb'
  simp only [CanTh.thetaChar_eq_theta] at h
  have key := two_dvd_of_entire_sign_periodic hτ hρ hρ0
    (N := fun n m => p ⬝ᵥ m - p' ⬝ᵥ m - (q ⬝ᵥ n - q' ⬝ᵥ n)) (fun n m z => by
      rw [← sub_eq_zero]
      refine entire_eq_zero_of_mul_continuous_eq_zero
        (f := fun z => ρ (z + τ *ᵥ ofIntVec n + ofIntVec m) - _ * ρ z)
        ((hρ.comp ((differentiable_id.add_const _).add_const _)).sub (hρ.const_mul _))
        (differentiable_theta hτ (fun k => (p' k : ℝ) / 2) (fun k => (q' k : ℝ) / 2)).continuous
        (theta_ne_zero hτ _ _) (fun z => ?_) z
      have h1 := h (z + τ *ᵥ ofIntVec n + ofIntVec m)
      rw [thetaQuasiPeriod_holds _ _ _ _ _ n m hτ.1, thetaQuasiPeriod_holds _ _ _ _ _ n m hτ.1, h] at h1
      have h2 : autFactor (fun k => (p k : ℝ) / 2) (fun k => (q k : ℝ) / 2) τ n m z =
          eC (((p ⬝ᵥ m - p' ⬝ᵥ m - (q ⬝ᵥ n - q' ⬝ᵥ n) : ℤ) : ℂ) / 2) *
            autFactor (fun k => (p' k : ℝ) / 2) (fun k => (q' k : ℝ) / 2) τ n m z := by
        have e : ∀ r s : Fin g → ℤ, ofRealVec (fun k => (r k : ℝ) / 2) ⬝ᵥ ofIntVec s = ((r ⬝ᵥ s : ℤ) : ℂ) / 2 :=
          fun r s => by
            simp only [dotProduct, ofRealVec, ofIntVec]
            push_cast
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun _ _ => by ring
        rw [autFactor, autFactor, ← mul_assoc, e, e, e, e]
        congr 1
        rw [← eC_add]
        congr 1
        push_cast
        ring
      rw [h2] at h1
      refine mul_left_cancel₀ (a := autFactor (fun k => (p' k : ℝ) / 2) (fun k => (q' k : ℝ) / 2) τ n m z)
        (mul_ne_zero (eC_ne_zero _) (eC_ne_zero _)) ?_
      linear_combination -h1)
  have e1 : p' = p := funext fun k => by
    have := key 0 (Pi.single k 1)
    simp only [dotProduct_single, dotProduct_zero, mul_one] at this
    have := hp k
    have := hp' k
    omega
  have e2 : q' = q := funext fun k => by
    have := key (Pi.single k 1) 0
    simp only [dotProduct_single, dotProduct_zero, mul_one] at this
    have := hq k
    have := hq' k
    omega
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

theorem thetaCharOff_congr {S : Finset (Fin g)} {τ τ' : Matrix (Fin g) (Fin g) ℂ} {a : Fin g → ℂ}
    (ha : ∀ k ∈ S, a k = 0) (hτ : ∀ k ∉ S, ∀ i, τ i k = τ' i k) (b z : Fin g → ℂ) :
    thetaCharOff S τ a b z = thetaCharOff S τ' a b z := by
  refine tsum_congr fun n => ?_
  have : τ *ᵥ ((fun i => (n.1 i : ℂ)) + a) = τ' *ᵥ ((fun i => (n.1 i : ℂ)) + a) := by
    funext i
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ S
    · simp [n.2 k hk, ha k hk]
    · simp only [hτ k hk i]
  rw [this]

end ThetaCompare

namespace AnArc

open ThetaCompare

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O}

theorem IsConvLine.BwMat_posDef {T₀ : ℝ} (hT : A.IsConvLine T₀) {w : ℂ} (hw : T₀ < w.im) : (A.BwMat w).PosDef := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let M : Matrix _ _ ℤ := Matrix.of fun i j => A.be (b i) (b j)
  have hM : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
    refine PolarisedLattice.real_pos_of_int_pos M (fun i j => A.be_symm _ _) fun x hx => ?_
    have h0 : ∑ i, x i • b i ≠ 0 := fun h =>
      hx (funext (Fintype.linearIndependent_iff.1 b.linearIndependent x h))
    have := A.be_pos _ h0
    convert this using 1
    simp only [M, dotProduct, mulVec, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hC : (A.BwMat (T₀ * Complex.I)).PosSemidef := by
    refine posSemidef_of_int_nonneg ?_ fun x => ?_
    · ext i j
      simp [BwMat_apply, A.Bw_symm _ (Module.Free.chooseBasis ℤ A.X i)]
    · have h1 : 0 ≤ A.Bw (T₀ * Complex.I) (∑ i, x i • b i) (∑ i, x i • b i) := by
        have := hT (∑ i, x i • b i)
        rw [Bw_eq]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
        linarith
      refine h1.trans_eq ?_
      simp only [dotProduct, mulVec, map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
        zsmul_eq_mul, Finset.mul_sum, BwMat_apply, b]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := (hM.smul (sub_pos.2 hw)).add_posSemidef hC
  convert this using 1
  ext i j
  simp [BwMat_apply, Bw_eq, M, b]; ring

section Coordinates

variable {g : ℕ} {Φ : A.V ≃ₗ[ℂ] (Fin g → ℂ)} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] A.La} {S : Finset (Fin g)}
  {τ : ℂ → Matrix (Fin g) (Fin g) ℂ}

theorem coord_Pw_of_basis (Φ : A.V →ₗ[ℂ] (Fin g → ℂ)) {w : ℂ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hP : ∀ k, Φ (A.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      Φ (A.Pw w (bas (Pi.single (.inr k) 1))) = τ *ᵥ Pi.single k 1) (u : Fin g ⊕ Fin g → ℤ) :
    Φ (A.Pw w (bas u)) = τ *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)) := by
  conv_lhs => rw [pi_eq_sum_univ' u]
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_zsmul, fun k => (hP k).1, fun k => (hP k).2]
  funext i
  simp [ofIntVec, mulVec, dotProduct, Pi.single_apply, mul_comm, add_comm]

theorem exists_form (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k))) :
    ∃ B : A.V →ₗ[ℂ] A.V →ₗ[ℂ] ℂ, (∀ v v', B v v' = B v' v) ∧ (∀ v l, B v (l, 0) = 0) ∧
      ∀ w u v, A.lin (bas u) v =
        B v (A.Pw w (bas u)) - 2 * Real.pi * Complex.I * (ofIntVec (fun k => u (.inr k)) ⬝ᵥ Φ v) := by
  let B : A.V →ₗ[ℂ] A.V →ₗ[ℂ] ℂ :=
    Fintype.linearCombination ℂ (fun j => A.lin (bas (Pi.single (.inl j) 1))) ∘ₗ Φ.toLinearMap
  have hE : ∀ w k, A.Pw w (bas (Pi.single (.inl k) 1)) = Φ.symm (Pi.single k 1) := fun w k => by
    rw [LinearEquiv.eq_symm_apply, hΦ]
    funext i
    simp [ofIntVec, mulVec, dotProduct, Pi.single_apply]
  have hB : ∀ k, B (Φ.symm (Pi.single k 1)) = A.lin (bas (Pi.single (.inl k) 1)) := fun k => by simp [B]
  have ext : ∀ {f f' : A.V →ₗ[ℂ] ℂ}, (∀ k, f (Φ.symm (Pi.single k 1)) = f' (Φ.symm (Pi.single k 1))) →
      ∀ v, f v = f' v := fun {f f'} h =>
    LinearMap.congr_fun (((Pi.basisFun ℂ (Fin g)).map Φ.symm).ext fun k => by simpa using h k)
  have key : ∀ w u v, A.lin (bas u) v =
      B v (A.Pw w (bas u)) - 2 * Real.pi * Complex.I * (ofIntVec (fun k => u (.inr k)) ⬝ᵥ Φ v) := fun w u => by
    refine ext (f' := B.flip (A.Pw w (bas u)) - (2 * Real.pi * Complex.I : ℂ) •
      (dotProductBilin ℂ ℂ (ofIntVec (fun k => u (.inr k))) ∘ₗ Φ.toLinearMap)) fun k => ?_
    have h1 := A.lin_Pw_sub w (bas u) (bas (Pi.single (.inl k) 1))
    rw [hEF, hE] at h1
    have h2 : omegaStd u (Pi.single (.inl k) 1) = -u (.inr k) := by simp [omegaStd, Pi.single_apply]
    rw [h2] at h1
    simp [hB, ofIntVec]
    push_cast at h1
    linear_combination h1
  refine ⟨B, fun v v' => ?_, fun v l => ?_, key⟩
  · refine ext (f := B v) (f' := B.flip v) (fun k => ?_) v'
    have h1 := key 0 (Pi.single (.inl k) 1) v
    rw [hE] at h1
    have h2 : ofIntVec (fun j => (Pi.single (.inl k) 1 : Fin g ⊕ Fin g → ℤ) (.inr j)) = 0 := by
      funext j; simp [ofIntVec]
    rw [LinearMap.flip_apply, hB, h1, h2, zero_dotProduct, mul_zero, sub_zero]
  · refine ext (f := B.flip (l, 0)) (f' := 0) (fun k => ?_) v
    rw [LinearMap.flip_apply, hB, lin_apply, (hS _).2 (by simp)]
    simp

theorem dot_coord_torus (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)))
    (u : Fin g ⊕ Fin g → ℤ) (l : A.X →+ ℂ) : ofIntVec (fun k => u (.inr k)) ⬝ᵥ Φ (l, 0) = l (bas u).y := by
  obtain ⟨B', hs, h0', key'⟩ := exists_form hEF hS hΦ
  have h := key' 0 u (l, 0)
  rw [hs, h0', lin_apply] at h
  simp only [H_zero_left, mul_zero, zero_sub, neg_inj] at h
  exact (mul_left_cancel₀ Complex.two_pi_I_ne_zero h).symm

theorem coord_torus_eq_zero (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)))
    (l : A.X →+ ℂ) {k : Fin g} (hk : k ∉ S) : Φ (l, 0) k = 0 := by
  have h := dot_coord_torus hEF hS hΦ (Pi.single (.inr k) 1) l
  rw [(hS _).2 (fun j hj => by simp [ne_of_mem_of_not_mem hj hk]), map_zero] at h
  simpa [ofIntVec, dotProduct, Pi.single_apply] using h

theorem tau_col_eq (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)))
    (w w' : ℂ) {k : Fin g} (hk : k ∉ S) (i : Fin g) : τ w i k = τ w' i k := by
  have hy : (bas (Pi.single (.inr k) 1)).y = 0 :=
    (hS _).2 fun j hj => by simp [ne_of_mem_of_not_mem hj hk]
  have h := congrFun ((hΦ w (Pi.single (.inr k) 1)).symm.trans
    ((congrArg Φ ((A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w hy).trans (A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w' hy).symm)).trans (hΦ w' _))) i
  simpa [ofIntVec, mulVec, dotProduct, Pi.single_apply] using h

theorem tau_isSymm (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)))
    (w : ℂ) : (τ w).IsSymm := by
  obtain ⟨B, hs, -, key⟩ := exists_form hEF hS hΦ
  refine IsSymm.ext fun j k => ?_
  have h := A.lin_Pw_sub w (bas (Pi.single (.inr j) 1)) (bas (Pi.single (.inr k) 1))
  rw [key w, key w, hs, hEF, hΦ, hΦ] at h
  have h2 : omegaStd (Pi.single (.inr j) 1) (Pi.single (.inr k) 1) = 0 := by simp [omegaStd]
  rw [h2] at h
  refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
  simp [ofIntVec, mulVec, dotProduct, Pi.single_apply] at h
  linear_combination h

theorem tau_mem_siegelH (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)))
    {w : ℂ} (hw : (A.BwMat w).PosDef) : τ w ∈ SiegelH (Fin g) := by
  have e1 : ∀ k, Φ (A.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 := fun k => by
    rw [hΦ]; funext i; simp [ofIntVec, mulVec, dotProduct, Pi.single_apply]
  have e2 : ∀ k, Φ (A.Pw w (bas (Pi.single (.inr k) 1))) = τ w *ᵥ Pi.single k 1 := fun k => by
    rw [hΦ]; funext i; simp [ofIntVec, mulVec, dotProduct, Pi.single_apply]
  refine ⟨tau_isSymm hEF hS hΦ w, im_posDef_of_hermForm (A.HwMat_isHermitian w Φ) (fun z hz => ?_)
    (fun j k => ?_) (fun j k => ?_)⟩
  · obtain ⟨v, rfl⟩ := Φ.surjective z
    rw [hermForm_HwMat]
    exact A.Hw_pos hw fun h => hz (by rw [h, map_zero])
  · rw [← e1 j, ← e1 k, hermForm_HwMat, A.im_Hw_Pw hw, hEF]
    simp [omegaStd]
  · rw [← e2 j, ← e1 k, hermForm_HwMat, A.im_Hw_Pw hw, hEF]
    simp [omegaStd, Pi.single_apply, eq_comm]

theorem exists_classical_law (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k))) :
    ∃ (B : A.V →ₗ[ℂ] A.V →ₗ[ℂ] ℂ) (χ : (Fin g → ℤ) → (Fin g → ℤ) → ℂ), (∀ v v', B v v' = B v' v) ∧
      (∀ v l, B v (l, 0) = 0) ∧ χ 0 0 = 1 ∧ (∀ n m, χ (-n) (-m) = χ n m) ∧ (∀ k ∈ S, χ 0 (Pi.single k 1) = 1) ∧
      ∀ w n m v, Complex.exp (-B (v + A.Pw w (bas (Sum.elim m n))) (v + A.Pw w (bas (Sum.elim m n)))) *
          A.perFactor w (bas (Sum.elim m n)) v =
        χ n m * eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ w *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ Φ v)) *
          Complex.exp (-B v v) := by
  obtain ⟨B, hs, h0, key⟩ := exists_form hEF hS hΦ
  refine ⟨(1 / 2 : ℂ) • B, fun n m => Complex.exp (A.logConst 0 (bas (Sum.elim m n)) -
    B (A.P0 (bas (Sum.elim m n))) (A.P0 (bas (Sum.elim m n))) / 2 +
    Real.pi * Complex.I * (ofIntVec n ⬝ᵥ τ 0 *ᵥ ofIntVec n)), fun v v' => by simp [hs v v'],
    fun v l => by simp [h0], ?_, fun n m => ?_, fun k hk => ?_, fun w n m v => ?_⟩
  · have : (Sum.elim 0 0 : Fin g ⊕ Fin g → ℤ) = 0 := by funext s; cases s <;> rfl
    simp [this, logConst, ofIntVec_zero]
  · have : (Sum.elim (-m) (-n) : Fin g ⊕ Fin g → ℤ) = -Sum.elim m n := by funext s; cases s <;> rfl
    simp [this, logConst, ofIntVec_neg, A.chi_neg, A.psi_neg, H_neg_left, H_neg_right, mulVec_neg]
  · obtain ⟨hy, hl⟩ := (A.orth_ker_iff (bas (Sum.elim (Pi.single k 1) 0))).1 fun v' hv' => by
      obtain ⟨u, rfl⟩ := bas.surjective v'
      simp [hEF, omegaStd, Pi.single_apply, (hS u).1 hv' k hk]
    beta_reduce
    generalize bas (Sum.elim (Pi.single k 1) 0) = la at hy hl
    have hP : A.P0 la = ((A.P0 la).1, 0) := Prod.ext rfl (by simp [hy, hl])
    rw [hP, h0]
    simp [logConst, hy, hl, ofIntVec_zero]
  · set u : Fin g ⊕ Fin g → ℤ := Sum.elim m n with hu
    have hN : ∀ v, B v (A.N (bas u)) = 0 := fun v => h0 v _
    have hPw : ∀ v, B v (A.Pw w (bas u)) = B v (A.P0 (bas u)) := fun v => by
      rw [Pw_apply, map_add, map_smul, hN, smul_zero, add_zero]
    have hPP : B (A.Pw w (bas u)) (A.Pw w (bas u)) = B (A.P0 (bas u)) (A.P0 (bas u)) := by
      rw [hPw, hs, hPw]
    have hq : ofIntVec n ⬝ᵥ Φ (A.N (bas u)) = 2 * A.q (bas u).y := by
      have h1 : ofIntVec n ⬝ᵥ Φ (A.N (bas u)) = (A.N (bas u)).1 (bas u).y := dot_coord_torus hEF hS hΦ u _
      rw [h1, N_fst_apply, ← two_mul_q]
      push_cast
      rfl
    have hτ : ofIntVec n ⬝ᵥ τ w *ᵥ ofIntVec n = ofIntVec n ⬝ᵥ τ 0 *ᵥ ofIntVec n + w * (2 * A.q (bas u).y) := by
      have h1 : Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec n + ofIntVec m := hΦ w u
      have h2 : Φ (A.Pw 0 (bas u)) = τ 0 *ᵥ ofIntVec n + ofIntVec m := hΦ 0 u
      rw [Pw_zero] at h2
      rw [Pw_apply, map_add, map_smul, h2] at h1
      have h3 := congrArg (ofIntVec n ⬝ᵥ ·) h1
      simp only [dotProduct_add, dotProduct_smul, hq, smul_eq_mul] at h3
      linear_combination -h3
    have hk : A.lin (bas u) v =
      B v (A.Pw w (bas u)) - 2 * Real.pi * Complex.I * (ofIntVec n ⬝ᵥ Φ v) := key w u v
    rw [perFactor_eq_exp, L_apply, eC, hk, hτ]
    simp only [← Complex.exp_add]
    congr 1
    simp only [map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hPP, hs (A.Pw w (bas u)) v, logConst]
    push_cast
    ring

theorem eq_mul_thetaCharOff (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (hΦ : ∀ w u, Φ (A.Pw w (bas u)) = τ w *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)))
    {th : (Fin A.gB → ℂ) → ℂ} {w : ℂ} {v : A.V}
    (hsum : Summable fun μ => A.term 1 0 th μ v * eTwoPi (w * A.exponent 1 0 μ))
    (hτ : τ w ∈ SiegelH (Fin g)) {a b : Fin g → ℝ} (ha : ∀ k ∈ S, a k = 0) {c : ℂ}
    (h : ∀ l, A.Sum 1 0 th w (v + (l, 0)) =
      c * thetaChar (τ w) (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (Φ (v + (l, 0)))) :
    th v.2 = c * thetaCharOff S (τ w) (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (Φ v) := by
  let p : (Fin g → ℤ) → A.X := fun n => (bas (Sum.elim 0 n)).y
  let G : A.X → ℂ := fun μ => ∑' n : p ⁻¹' {μ}, c * CanTh.thTerm (τ w) a b (Φ v) n
  have hG : ∀ l : A.X →+ ℂ, HasSum (fun μ => G μ * eTwoPi (l μ)) (A.Sum 1 0 th w (v + (l, 0))) := fun l => by
    have h1 := ((CanTh.hasSum_thTerm (CanTh.mem_thetaDomain hτ.2) a b (Φ (v + (l, 0)))).mul_left c).tsum_fiberwise p
    rw [← h] at h1
    refine (funext fun μ => ?_ : (fun μ => G μ * eTwoPi (l μ)) = _) ▸ h1
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    have h2 : ofIntVec n.1 ⬝ᵥ Φ (l, 0) = l (p n.1) := dot_coord_torus hEF hS hΦ (Sum.elim 0 n.1) l
    have h3 : (fun i => (a i : ℂ)) ⬝ᵥ Φ (l, 0) = 0 := Finset.sum_eq_zero fun k _ => by
      by_cases hk : k ∈ S
      · simp [ha k hk]
      · simp [coord_torus_eq_zero hEF hS hΦ l hk]
    rw [show p n.1 = μ from n.2] at h2
    rw [map_add, CanTh.thTerm_add_var, add_dotProduct, h3, add_zero, ← h2, e_def]
    change _ = c * (Complex.exp (_ * (ofIntVec n.1 ⬝ᵥ _)) * _)
    ring
  have hF : ∀ (l : A.X →+ ℂ) μ, A.term 1 0 th μ (v + (l, 0)) * eTwoPi (w * A.exponent 1 0 μ) =
      A.term 1 0 th μ v * eTwoPi (w * A.exponent 1 0 μ) * eTwoPi (l μ) := fun l μ => by
    simp [term, e_add]; ring
  have hGs : Summable G := by simpa using (hG 0).summable
  have hz := A.eq_zero_of_tsum_char (hsum.sub hGs) fun l hl => by
    have hs1 : Summable fun μ => A.term 1 0 th μ v * eTwoPi (w * A.exponent 1 0 μ) * eTwoPi (l μ) := by
      refine Summable.of_norm ?_
      simpa [norm_e, hl] using hsum.norm
    simp only [sub_mul]
    rw [hs1.tsum_sub (hG l).summable, (hG l).tsum_eq, Sum]
    simp only [hF, sub_self]
  have h0 := congrFun hz 0
  simp only [term, psi_zero, Units.val_one, one_pow, map_zero, e_zero, smul_zero, add_zero, one_mul, exponent_zero,
    Int.cast_zero, mul_zero, mul_one, Pi.zero_apply, sub_eq_zero] at h0
  rw [h0, thetaCharOff, ← tsum_mul_left]
  exact (Equiv.subtypeEquivRight (p := fun n => n ∈ p ⁻¹' {0}) (q := fun n => ∀ k ∈ S, n k = 0)
    fun n => hS (Sum.elim 0 n)).symm.tsum_eq _ |>.symm

end Coordinates

theorem theta_comparison (A : AnArc O) {T₀ : ℝ} (hT : A.IsConvLine T₀) {g : ℕ} (h₀ : A.V ≃ₗ[ℂ] (Fin g → ℂ))
    {th : (Fin A.gB → ℂ) → ℂ} (hth : th ∈ A.Theta 1 0) (hne : th ≠ 0)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] A.La) (hEF : ∀ u v, A.EF (bas u) (bas v) = -omegaStd u v)
    (S : Finset (Fin g)) (hS : ∀ u, (bas u).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0)
    (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ)
    (hP : ∀ w k, h *ᵥ h₀ (A.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h *ᵥ h₀ (A.Pw w (bas (Pi.single (.inr k) 1))) = τ w *ᵥ Pi.single k 1) :
    IsUnit h ∧ (∀ w : ℂ, T₀ < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef) ∧
    ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ (∀ k ∈ S, c₁ k = 0) ∧
      (∃ (Q : A.V → ℂ) (κ : ℂ),
        (∃ B : A.V →ₗ[ℂ] A.V →ₗ[ℂ] ℂ, (∀ v v', B v v' = B v' v) ∧ ∀ v, Q v = B v v) ∧
        Differentiable ℂ Q ∧ Q 0 = 0 ∧ κ ≠ 0 ∧
        (∀ w : ℂ, T₀ < w.im → ∀ v,
          A.Sum 1 0 th w v = κ * Complex.exp (Q v) * thetaChar (τ w) c₁ c₂ (h *ᵥ h₀ v)) ∧
        ∀ (w : ℂ) v, th v.2 = κ * Complex.exp (Q v) * thetaCharOff S (τ w) c₁ c₂ (h *ᵥ h₀ v)) ∧
      ∀ c₁' c₂' : Fin g → ℂ, (∀ k, c₁' k = 0 ∨ c₁' k = 1 / 2) → (∀ k, c₂' k = 0 ∨ c₂' k = 1 / 2) →
        ∀ w₁ : ℂ, T₀ < w₁.im → ∀ f : A.V → ℂ, Differentiable ℂ f → (∀ v, f v ≠ 0) →
          (∀ v, A.Sum 1 0 th w₁ v = f v * thetaChar (τ w₁) c₁' c₂' (h *ᵥ h₀ v)) → c₁' = c₁ ∧ c₂' = c₂ := by
  have hu : IsUnit h := mulVec_surjective_iff_isUnit.1 fun z =>
    ⟨∑ k, z k • h₀ (A.Pw 0 (bas (Pi.single (.inl k) 1))), by
      simp only [mulVec_sum, mulVec_smul, fun k => (hP 0 k).1]
      exact (pi_eq_sum_univ' z).symm⟩
  let Φ : A.V ≃ₗ[ℂ] (Fin g → ℂ) := h₀.trans (LinearEquiv.ofBijective h.mulVecLin
    ⟨mulVec_injective_iff_isUnit.2 hu, mulVec_surjective_iff_isUnit.2 hu⟩)
  have eΦ : ∀ v, h *ᵥ h₀ v = Φ v := fun _ => rfl
  simp only [eΦ] at hP ⊢
  clear_value Φ
  have hΦ := fun w u => coord_Pw_of_basis (bas := bas) Φ.toLinearMap (hP w) u
  simp only [LinearEquiv.coe_coe] at hΦ
  have hτ : ∀ w : ℂ, T₀ < w.im → τ w ∈ SiegelH (Fin g) := fun w hw =>
    tau_mem_siegelH hEF hS hΦ (hT.BwMat_posDef hw)
  obtain ⟨B, χ, hs, hB0, hχ0, hχn, hχS, law⟩ := exists_classical_law hEF hS hΦ
  have hQ : Differentiable ℂ fun v => B v v := by
    let B' : A.V →L[ℂ] A.V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (A.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ B)
    exact B'.differentiable.clm_apply differentiable_id
  have hΦd : Differentiable ℂ Φ.symm := Φ.symm.toContinuousLinearEquiv.differentiable
  let F : ℂ → (Fin g → ℂ) → ℂ := fun w z =>
    Complex.exp (-B (Φ.symm z) (Φ.symm z)) * A.Sum 1 0 th w (Φ.symm z)
  have hSF : ∀ w v, A.Sum 1 0 th w v = Complex.exp (B v v) * F w (Φ v) := fun w v => by
    simp only [F, LinearEquiv.symm_apply_apply, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      one_mul]
  have hF0 : ∀ w : ℂ, T₀ < w.im → F w ≠ 0 := fun w hw h0 => by
    obtain ⟨v, hv⟩ := A.exists_Sum_ne_zero one_ne_zero 0 hne fun z => summable_term hT one_ne_zero hth hw (0, z)
    exact hv (by rw [hSF, h0, Pi.zero_apply, mul_zero])
  have hFd : ∀ w : ℂ, T₀ < w.im → Differentiable ℂ (F w) := fun w hw =>
    (hQ.comp hΦd).neg.cexp.mul ((differentiable_Sum hT one_ne_zero hth hw).comp hΦd)
  have hFl : ∀ w n m z, F w (z + τ w *ᵥ ofIntVec n + ofIntVec m) =
      χ n m * eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ w *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F w z := by
    intro w n m z
    obtain ⟨v, rfl⟩ := Φ.surjective z
    have e : Φ v + τ w *ᵥ ofIntVec n + ofIntVec m = Φ (v + A.Pw w (bas (Sum.elim m n))) := by
      rw [map_add, hΦ, add_assoc]; rfl
    simp only [e, F, LinearEquiv.symm_apply_apply]
    rw [A.Sum_add_period hth, pow_one, ← mul_assoc, law, mul_assoc]
  have hw₀ : T₀ < (((T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  obtain ⟨a, b, ha, hb, hab⟩ := exists_half_char_of_even
    (multiplier_add_of_ne_zero (hτ _ hw₀).1 (hF0 _ hw₀) (hFl _)) hχ0 hχn
  have haS : ∀ k ∈ S, a k = 0 := fun k hk => (ha k).resolve_right fun h2 => by
    have h1 := hχS k hk
    have h3 : ofRealVec a ⬝ᵥ ofIntVec (Pi.single k 1) - ofRealVec b ⬝ᵥ ofIntVec 0 = -((-1 : ℤ) : ℂ) / 2 := by
      simp [ofRealVec, ofIntVec, dotProduct, Pi.single_apply, h2]
    rw [hab, h3, eC_neg_half_int] at h1
    norm_num at h1
  have hc : ∀ w : ℂ, T₀ < w.im → ∃ c : ℂ, ∀ v, A.Sum 1 0 th w v =
      c * Complex.exp (B v v) * thetaChar (τ w) (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (Φ v) := fun w hw => by
    have hmem : F w ∈ thetaLevelChar a b 1 (τ w) :=
      ⟨hFd w hw, fun n m z => by rw [hFl, hab, Nat.cast_one, one_mul]⟩
    rw [thetaLevelChar_one (hτ w hw), Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, fun v => ?_⟩
    rw [hSF, ← hc, CanTh.thetaChar_eq_theta, Pi.smul_apply, smul_eq_mul]
    ring
  choose c hc using hc
  have hoff : ∀ (w : ℂ) (hw : T₀ < w.im) (w' : ℂ) v, th v.2 =
      c w hw * Complex.exp (B v v) * thetaCharOff S (τ w') (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) (Φ v) := by
    intro w hw w' v
    rw [thetaCharOff_congr (fun k hk => by simp [haS k hk]) (fun k hk i => tau_col_eq hS hΦ w' w hk i)]
    refine eq_mul_thetaCharOff hEF hS hΦ (summable_term hT one_ne_zero hth hw v) (hτ w hw) haS fun l => ?_
    rw [hc w hw]
    simp only [map_add, LinearMap.add_apply, hB0, hs (l, 0) v, add_zero]
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  have hcc : ∀ w hw, c w hw = c _ hw₀ := fun w hw => by
    have h1 := hoff w hw 0 (0, z₀)
    have h2 := hoff _ hw₀ 0 (0, z₀)
    rw [mul_assoc] at h1 h2
    exact mul_right_cancel₀ (right_ne_zero_of_mul (h1 ▸ hz₀)) (h1.symm.trans h2)
  have hκ : c _ hw₀ ≠ 0 := fun h0 => hz₀ (by
    have := hoff _ hw₀ 0 (0, z₀)
    rwa [h0, zero_mul, zero_mul] at this)
  have half : ∀ {a : Fin g → ℝ}, (∀ k, a k = 0 ∨ a k = 1 / 2) → ∀ k, (a k : ℂ) = 0 ∨ (a k : ℂ) = 1 / 2 :=
    fun ha k => (ha k).imp (fun h => by simp [h]) fun h => by simp [h]
  refine ⟨hu, hτ, fun i => a i, fun i => b i, half ha, half hb, fun k hk => by simp [haS k hk],
    ⟨fun v => B v v, c _ hw₀, ⟨B, hs, fun _ => rfl⟩, hQ, by simp, hκ, fun w hw v => by rw [hc w hw, hcc],
      hoff _ hw₀⟩, fun c₁' c₂' h1 h2 w₁ hw₁ f hf hf0 hfS => ?_⟩
  refine char_eq_of_thetaChar_eq_mul (hτ w₁ hw₁) (half ha) (half hb) h1 h2
    (ρ := fun z => (c _ hw₀)⁻¹ * Complex.exp (-B (Φ.symm z) (Φ.symm z)) * f (Φ.symm z))
    (((hQ.comp hΦd).neg.cexp.const_mul _).mul (hf.comp hΦd))
    (mul_ne_zero (mul_ne_zero (inv_ne_zero hκ) (Complex.exp_ne_zero _)) (hf0 _)) fun z => ?_
  obtain ⟨v, rfl⟩ := Φ.surjective z
  have h3 := hfS v
  rw [hc w₁ hw₁, hcc] at h3
  simp only [LinearEquiv.symm_apply_apply]
  rw [mul_assoc, ← h3, Complex.exp_neg]
  have := Complex.exp_ne_zero (B v v)
  field_simp

example (τ₀ : ℂ) : ∃ (h₀ : (tate τ₀).V ≃ₗ[ℂ] (Fin 1 → ℂ)) (bas : (Fin 1 ⊕ Fin 1 → ℤ) ≃ₗ[ℤ] (tate τ₀).La),
    (∀ u v, (tate τ₀).EF (bas u) (bas v) = -omegaStd u v) ∧
    (∀ u, (bas u).y = 0 ↔ ∀ k ∈ (Finset.univ : Finset (Fin 1)), u (.inr k) = 0) ∧
    ∀ w k, (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ h₀ ((tate τ₀).Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ h₀ ((tate τ₀).Pw w (bas (Pi.single (.inr k) 1))) =
        !![τ₀ + 2 * w] *ᵥ Pi.single k 1 := by
  let h₀ : ((ℤ →+ ℂ) × (Fin 0 → ℂ)) ≃ₗ[ℂ] (Fin 1 → ℂ) :=
    { toFun := fun v _ => v.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun z => (zmultiplesHom ℂ (z 0), 0)
      left_inv := fun v => Prod.ext (AddMonoidHom.ext_int (by simp)) (Subsingleton.elim _ _)
      right_inv := fun z => funext fun i => by simp [Subsingleton.elim i 0] }
  let bas : (Fin 1 ⊕ Fin 1 → ℤ) ≃+ (ℤ × (ℤ →+ ℤ) × (⊥ : Submodule ℤ (Fin 0 → ℂ))) :=
    { toFun := fun u => (u (.inr 0), zmultiplesHom ℤ (u (.inl 0)), 0)
      map_add' := fun u u' => Prod.ext rfl (Prod.ext (AddMonoidHom.ext_int (by simp)) (Subsingleton.elim _ _))
      invFun := fun p => Sum.elim (fun _ => p.2.1 1) fun _ => p.1
      left_inv := fun u => funext fun s => by rcases s with i | i <;> simp [Subsingleton.elim i 0]
      right_inv := fun p => Prod.ext rfl (Prod.ext (AddMonoidHom.ext_int (by simp)) (Subsingleton.elim _ _)) }
  refine ⟨h₀, AddEquiv.toIntLinearEquiv (M₂ := (tate τ₀).La) bas, fun u v => ?_, fun u => ?_, fun w k => ?_⟩
  · change zmultiplesHom ℤ (v (.inl 0)) (u (.inr 0)) - zmultiplesHom ℤ (u (.inl 0)) (v (.inr 0)) + 0 = _
    simp [omegaStd, mul_comm]
  · change u (.inr 0) = 0 ↔ _
    simp
  · rw [one_mulVec, one_mulVec, Subsingleton.elim k 0]
    refine ⟨funext fun i => (tate_Pw τ₀ w _ _).trans ?_, funext fun i => (tate_Pw τ₀ w _ _).trans ?_⟩ <;>
      simp [Subsingleton.elim i 0]

end AnArc

end GlobalTheory

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

noncomputable section

open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.ThetaPoint

open CanTh

variable {g : ℕ}

theorem isSymm_and_eq_imInv {M τ : Matrix (Fin g) (Fin g) ℂ} (hH : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) (hτ : (τ.map Complex.im).PosDef)
    {s : ℝ} (hs : s = 1 ∨ s = -1)
    (h₁₁ : ∀ i j, (hermForm M (Pi.single i 1) (Pi.single j 1)).im = 0)
    (h₁₂ : ∀ i j, (hermForm M (Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = if i = j then s else 0)
    (h₂₂ : ∀ i j, (hermForm M (τ *ᵥ Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = 0) :
    τ.IsSymm ∧ M = imInv τ := by
  let Y : Matrix (Fin g) (Fin g) ℝ := M.map Complex.re
  have hY : M = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · have := h₁₁ i j
      rw [hermForm, SiegelNormalForm.form_single] at this
      simpa using this
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (hH.apply i j)
    simpa [Y] using this
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : (fun i => (a i : ℂ)) ≠ 0 := fun h0 =>
      ha (funext fun i => by simpa using congrFun h0 i)
    have := hpos _ hne
    rw [hY] at this
    simpa [hermForm, Matrix.mulVec, dotProduct] using this
  rw [hY] at h₁₂ h₂₂
  rcases hs with rfl | rfl
  · obtain ⟨-, h2, -⟩ := SiegelNormalForm.siegel_of_relations Y hYp (-τ)
      (fun i j => by
        have := h₁₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg, Complex.neg_im, this]
        split_ifs <;> simp)
      (fun i j => by
        have := h₂₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg,
          neg_dotProduct, neg_neg, this])
    have hf : ∀ i : Fin g, False := fun i => by
      have e1 := h2.diag_pos (i := i)
      have e2 := hτ.diag_pos (i := i)
      simp only [Matrix.map_apply, Matrix.neg_apply, Complex.neg_im] at e1 e2
      linarith
    exact ⟨by ext i; exact (hf i).elim, by ext i; exact (hf i).elim⟩
  · obtain ⟨h1, -, h3⟩ := SiegelNormalForm.siegel_of_relations Y hYp τ h₁₂ h₂₂
    refine ⟨h1, ?_⟩
    rw [hY, imInv, Matrix.inv_eq_left_inv h3]

def lawSubgroup {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] (ι : Λ →+ V) (J : Λ → V → ℂ)
    (hJ : ∀ l z, J l z ≠ 0) (hc : ∀ l m z, J (l + m) z = J l (z + ι m) * J m z) (θ : V → ℂ) :
    AddSubgroup Λ where
  carrier := {l | ∀ z, θ (z + ι l) = J l z * θ z}
  zero_mem' := fun z => by
    have h := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h
    rw [map_zero, add_zero, (mul_eq_left₀ (hJ 0 z)).1 h.symm, one_mul]
  add_mem' := fun {l m} hl hm z => by
    rw [map_add, add_comm (ι l), ← add_assoc, hl, hm, hc, mul_assoc]
  neg_mem' := fun {l} hl z => by
    have h0 := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h0
    have h1 := hc l (-l) z
    rw [add_neg_cancel, (mul_eq_left₀ (hJ 0 z)).1 h0.symm] at h1
    have h2 := hl (z + ι (-l))
    rw [add_assoc, ← map_add, neg_add_cancel, map_zero, add_zero] at h2
    rw [h2, ← mul_assoc, mul_comm (J (-l) z), ← h1, one_mul]

theorem exists_half_of_sq_eq_one {c : ℂ} (hc : c ^ 2 = 1) :
    ∃ a : ℝ, (a = 0 ∨ a = 1 / 2) ∧ cexp (2 * π * I * a) = c ∧ cexp (-(2 * π * I * a)) = c := by
  rcases sq_eq_one_iff.1 hc with rfl | rfl
  · exact ⟨0, Or.inl rfl, by simp, by simp⟩
  · refine ⟨1 / 2, Or.inr rfl, ?_, ?_⟩
    · rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
    · rw [← Complex.exp_neg_pi_mul_I]; congr 1; push_cast; ring

theorem exists_half_char {d : ℕ} (Λ : Submodule ℤ (Fin d → ℂ)) (Hm : Matrix (Fin d) (Fin d) ℂ) (χ : Λ → ℂ)
    (Φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef)
    (hform : ∀ z w, hermForm Hm (Φ z) (Φ w) = hermForm (imInv τ) z w)
    (hΛ : ∀ z, Φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ))
    (hχ : ∀ l, χ l ^ 2 = 1)
    (hc : ∀ (l m : Λ) z, χ (l + m) * cexp (π * hermForm Hm z (l + m : Λ) + π / 2 * hermForm Hm (l + m : Λ) (l + m : Λ)) =
      χ l * cexp (π * hermForm Hm (z + m) l + π / 2 * hermForm Hm l l) *
        (χ m * cexp (π * hermForm Hm z m + π / 2 * hermForm Hm m m))) :
    ∃ a b : Fin g → ℝ, (∀ k, a k = 0 ∨ a k = 1 / 2) ∧ (∀ k, b k = 0 ∨ b k = 1 / 2) ∧
      ∀ (l : Λ) z, canTh τ a b (Φ.symm (z + l)) =
        χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) * canTh τ a b (Φ.symm z) := by
  have hsingle : ∀ j : Fin g, (fun i => (((Pi.single j (1 : ℤ) : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j (1 : ℂ) := by
    intro j
    ext i
    by_cases hij : i = j <;> simp [Pi.single_apply, hij]
  have hzero : (fun i => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by ext i; simp
  let e : Fin g → Λ := fun i => ⟨Φ (Pi.single i 1), (hΛ _).2 ⟨Pi.single i 1, 0, by
    rw [hsingle, hzero, mulVec_zero, add_zero]⟩⟩
  let f : Fin g → Λ := fun i => ⟨Φ (τ *ᵥ Pi.single i 1), (hΛ _).2 ⟨0, Pi.single i 1, by
    rw [hsingle, hzero, zero_add]⟩⟩
  choose a ha ha' _ using fun i => exists_half_of_sq_eq_one (hχ (e i))
  choose b hb _ hb' using fun i => exists_half_of_sq_eq_one (hχ (f i))
  refine ⟨a, b, ha, hb, fun l => ?_⟩
  let S := lawSubgroup Λ.subtype.toAddMonoidHom
    (fun l z => χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))
    (fun l z => mul_ne_zero (fun h => by simpa [h] using hχ l) (Complex.exp_ne_zero _)) hc
    (fun z => canTh τ a b (Φ.symm z))
  have key : ∀ (l : Λ) (m n : Fin g → ℤ), (l : Fin d → ℂ) = Φ ((fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) →
      canMult a b m n = χ l → l ∈ S := fun l m n hl hm z => by
    obtain ⟨z, rfl⟩ := Φ.surjective z
    change canTh τ a b (Φ.symm (Φ z + l)) = χ l * cexp (π * hermForm Hm (Φ z) l + π / 2 * hermForm Hm l l) *
      canTh τ a b (Φ.symm (Φ z))
    rw [hl, ← map_add, Φ.symm_apply_apply, Φ.symm_apply_apply, hform, hform,
      canTh_add_period hs hp a b m n rfl, hm]
  have he : ∀ i, e i ∈ S := fun i => key _ (Pi.single i 1) 0
    (by rw [hsingle, hzero, mulVec_zero, add_zero]) (by
      rw [← ha', canMult]
      congr 1
      simp [dotProduct, Pi.single_apply])
  have hf : ∀ i, f i ∈ S := fun i => key _ 0 (Pi.single i 1)
    (by rw [hsingle, hzero, zero_add]) (by
      rw [← hb', canMult]
      congr 1
      simp [dotProduct, Pi.single_apply])
  obtain ⟨m, n, hmn⟩ := (hΛ (Φ.symm l)).1 (by rw [Φ.apply_symm_apply]; exact l.2)
  have hl : l = ∑ i, m i • e i + ∑ i, n i • f i := by
    apply Subtype.ext
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [← Φ.apply_symm_apply l, hmn, h1 m, h1 n]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_add, map_sum, map_zsmul, e, f]
    simp
  have : l ∈ S := hl ▸ S.add_mem (S.sum_mem fun i _ => S.zsmul_mem (he i) _)
    (S.sum_mem fun i _ => S.zsmul_mem (hf i) _)
  exact this

theorem half_char_unique {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    {a b a' b' : Fin g → ℝ} (ha : ∀ k, a k = 0 ∨ a k = 1 / 2) (hb : ∀ k, b k = 0 ∨ b k = 1 / 2)
    (ha' : ∀ k, a' k = 0 ∨ a' k = 1 / 2) (hb' : ∀ k, b' k = 0 ∨ b' k = 1 / 2)
    {U : (Fin g → ℂ) → ℂ} (hU : Differentiable ℂ U) (hU0 : ∀ z, U z ≠ 0)
    (h : ∀ z, theta a' b' z τ = U z * theta a b z τ) : a' = a ∧ b' = b := by
  have H₁ : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z,
        (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') =
          eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧
        (fun z => theta 0 0 z τ) ≠ 0 := fun g τ hτ => by
    refine ⟨⟨?_, fun n n' z => ?_⟩, theta_ne_zero hτ 0 0⟩
    · have := differentiable_thetaChar (mem_thetaDomain hτ.2) 0 0
      simpa only [← thetaChar_eq_theta] using this
    · have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
      simp only [thetaQuasiPeriod_holds (Fin g) 0 0 z τ n n' hτ.1, autFactor, h0, zero_dotProduct, sub_zero, eC_zero,
        one_mul]
      congr 2
      ring
  let p : (Fin g → ℝ) → (Fin g → ℝ) → (Fin g → ℂ) → ℂ := fun a b z =>
    eC (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b + ofRealVec 0))
  have hp0 : ∀ a b z, p a b z ≠ 0 := fun a b z => Complex.exp_ne_zero _
  have hpd : ∀ a b, Differentiable ℂ (p a b) := fun a b => by
    simp only [p, eC, dotProduct]
    fun_prop
  have sh : ∀ a b z, theta a b z τ = p a b z * theta 0 0 (z + τ *ᵥ ofRealVec a + ofRealVec b) τ := fun a b z => by
    simpa only [zero_add] using thetaCharShift_holds (Fin g) a b 0 0 z τ hs
  let v := τ *ᵥ ofRealVec a + ofRealVec b
  obtain ⟨n, n', hn⟩ := mem_periodLattice_of_theta_translate_eq_unit_mul H₁
    periodLattice_isLattice_of_mem_siegelH g τ ⟨hs, hp⟩ (τ *ᵥ ofRealVec a' + ofRealVec b' - v)
    (fun z => U (z - v) * p a b (z - v) * (p a' b' (z - v))⁻¹)
    (((hU.comp (differentiable_id.sub_const v)).mul ((hpd a b).comp (differentiable_id.sub_const v))).mul
      (((hpd a' b').comp (differentiable_id.sub_const v)).inv fun z => hp0 _ _ _))
    (fun z => mul_ne_zero (mul_ne_zero (hU0 _) (hp0 _ _ _)) (inv_ne_zero (hp0 _ _ _))) (fun z => by
      have e := h (z - v)
      rw [sh a' b', sh a b, show z - v + τ *ᵥ ofRealVec a + ofRealVec b = z by simp only [v]; abel,
        show z - v + τ *ᵥ ofRealVec a' + ofRealVec b' = z + (τ *ᵥ ofRealVec a' + ofRealVec b' - v) by abel] at e
      have := hp0 a' b' (z - v)
      field_simp
      linear_combination e)
  have him : (τ.map Complex.im) *ᵥ (a' - a - fun i => (n i : ℝ)) = 0 := by
    ext i
    have := congrArg Complex.im (congrFun hn i)
    simp only [v, mulVec, dotProduct, ofRealVec, ofIntVec, Pi.add_apply, Pi.sub_apply, add_im, sub_im, im_sum,
      mul_im, ofReal_re, ofReal_im, intCast_re, intCast_im, mul_zero, zero_add, add_zero] at this
    simp only [mulVec, dotProduct, map_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    linarith
  have h1 : (a' - a - fun i => (n i : ℝ)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit) (him.trans (mulVec_zero _).symm)
  have half : ∀ (x y : ℝ) (k : ℤ), (x = 0 ∨ x = 1 / 2) → (y = 0 ∨ y = 1 / 2) → x - y = k → x = y ∧ k = 0 := by
    intro x y k hx hy e
    have h1 : (-1 : ℝ) < k := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h2 : (k : ℝ) < 1 := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h3 : k = 0 := by
      have : (-1 : ℤ) < k := by exact_mod_cast h1
      have : k < 1 := by exact_mod_cast h2
      omega
    subst h3
    exact ⟨by simpa [sub_eq_zero] using e, rfl⟩
  have h2 := fun i => half _ _ (n i) (ha' i) (ha i) (sub_eq_zero.1 (congrFun h1 i))
  obtain rfl : a' = a := funext fun i => (h2 i).1
  obtain rfl : n = 0 := funext fun i => (h2 i).2
  refine ⟨rfl, funext fun i => (half _ _ (n' i) (hb' i) (hb i) ?_).1⟩
  simp only [v, ofIntVec_zero, mulVec_zero, zero_add, add_sub_add_left_eq_sub] at hn
  have := congrFun hn i
  simp only [Pi.sub_apply, ofRealVec, ofIntVec] at this
  exact_mod_cast this

end GlobalTheory.ThetaPoint

import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_frame {r n : ℕ} (h : r + 1 = n) (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G) (I : Matrix (Fin n) (Fin r) ℂ)
    (Z : Matrix (Fin n) (Fin 1) ℂ) (FA : Matrix (Fin r) (Fin r) ℂ) (hA : IsUnit FA) (εA : Fin r → Bool)
    (h1 : Iᴴ * G * I = FAᴴ * Formalism.REAL.Jm εA * FA) (h2 : Iᴴ * G * Z = 0) (h3 : Zᴴ * G * Z = 1) :
    ∃ (ε : Fin n → Bool) (FB : Matrix (Fin n) (Fin n) ℂ), IsUnit FB ∧ FBᴴ * Formalism.REAL.Jm ε * FB = G ∧
      ∀ (y : Fin r → ℂ) (a : ℂ), eu (FB *ᵥ (I *ᵥ y + a • fun i => Z i 0)) ^ 2 = eu (FA *ᵥ y) ^ 2 + ‖a‖ ^ 2 := by
  let e : Fin r ⊕ Fin 1 ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  let P : Matrix (Fin n) (Fin n) ℂ := (fromCols I Z).submatrix id e.symm
  let Q : Matrix (Fin n) (Fin n) ℂ := (fromBlocks FA 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm
  let ε : Fin n → Bool := fun i => Sum.elim εA (fun _ => true) (e.symm i)
  have hJ : Formalism.REAL.Jm ε = (fromBlocks (Formalism.REAL.Jm εA) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [ε, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply]
  have h4 : Zᴴ * G * I = 0 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have key : Pᴴ * G * P = Qᴴ * Formalism.REAL.Jm ε * Q := by
    have a1 : Pᴴ * G * P = ((fromCols I Z)ᴴ * G * fromCols I Z).submatrix e.symm e.symm := rfl
    rw [a1, hJ]
    simp only [Q, conjTranspose_submatrix, submatrix_mul_equiv]
    congr 1
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, h1, h2, h3, h4,
      fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hQ : IsUnit Q := by
    rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
    simpa [Q, det_submatrix_equiv_self, det_fromBlocks_zero₂₁] using hA
  have hJ2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, diagonal_mul_diagonal]
    rw [← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hP : IsUnit P.det := by
    have hd := congrArg det key
    have q := ((Matrix.isUnit_iff_isUnit_det _).1 hQ).ne_zero
    have j : (Formalism.REAL.Jm ε).det ≠ 0 := fun h0 => by
      have := congrArg det hJ2
      rw [det_mul, h0, det_one] at this; simp at this
    simp only [det_mul, det_conjTranspose] at hd
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hd
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 q) j) q hd.symm
  refine ⟨ε, Q * P⁻¹, hQ.mul ((Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 hP)), ?_, fun y a => ?_⟩
  · calc (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᴴ * G * (P * P⁻¹) := by rw [← key]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [Matrix.mul_nonsing_inv _ hP]; simp
  · have b1 : I *ᵥ y + a • (fun i => Z i 0) = P *ᵥ (Sum.elim y (fun _ => a) ∘ e.symm) := by
      simp only [P]
      rw [submatrix_mulVec_equiv]
      funext i
      simp [mulVec, dotProduct, Function.comp_def, mul_comm]
    rw [b1, mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hP]
    simp only [Q]
    rw [submatrix_mulVec_equiv]
    simp only [eu]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp]
    simp [Function.comp_def, fromBlocks_mulVec]

variable {D : D7}

theorem exists_adapted {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B₀ : Fr V) : ∃ B : Fr V, Adapted d A B := by
  have hm : ∀ τ {a b : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E) (Z : Matrix (Fin V.rank) (Fin b) D.host.E),
      (X.map (tauE D τ))ᴴ * gramAt D V τ * Z.map (tauE D τ) = (Xᴴ * V.gram * Z).map (tauE D τ) := fun τ a b X Z => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl
  have H := fun τ => exists_frame d.rank (gramAt D V τ)
    (by rw [← B₀.fr_gram τ]
        have : (Formalism.REAL.Jm (B₀.ε τ))ᴴ = Formalism.REAL.Jm (B₀.ε τ) := by
          rw [Formalism.REAL.Jm, diagonal_conjTranspose]; congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, this, Matrix.mul_assoc])
    ((frameMat V Y d.ι).map (tauE D τ)) (d.a.map (tauE D τ)) (A.fr τ) (A.fr_unit τ) (A.ε τ)
    (by rw [hm, GlobalTheory.RowUnf.frameMat_isom d, A.fr_gram]; rfl)
    (by rw [hm, show (frameMat V Y d.ι)ᴴ * V.gram * d.a = 0 from d.perp]; ext i j; simp)
    (by rw [hm, show d.aᴴ * V.gram * d.a = antiDiagonalSignGramMatrix 1 1 from d.gram]; ext i j
        obtain rfl := Subsingleton.elim i j
        simp [antiDiagonalSignGramMatrix, Matrix.one_apply])
  choose ε fr h1 h2 h3 using H
  exact ⟨⟨ε, fr, h1, h2⟩, h3⟩

theorem decayAt_of_pos {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (hε : ∀ i, M.ε τ i = true)
    (v a : M.H τ) (N : ℕ) : DecayAt M τ v a N := by
  have hJ : Formalism.REAL.Jm (M.ε τ) = 1 := by simp [Formalism.REAL.Jm, hε]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  refine ⟨‖v‖ * ‖a‖ * (1 + Real.sqrt (∑ i, ∑ j, (∑ l, (∑ k, ‖(M.fr τ)⁻¹ i k‖) * ‖M.fr τ l j‖) ^ 2)) ^ N, fun g hg => ?_⟩
  set u := M.fr τ * g * (M.fr τ)⁻¹ with hu
  have hg' : gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g = (M.fr τ)ᴴ * M.fr τ := by
    have := M.fr_gram τ
    rw [hJ, Matrix.mul_one] at this
    rw [this]; exact hg
  have h1 : uᴴ * u = 1 := by
    calc uᴴ * u = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [hu, conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * (M.fr τ * (M.fr τ)⁻¹) := by rw [hg']; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have h2 : u ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
    show uᴴ * _ * u = _
    rw [hJ, Matrix.mul_one, h1]
  have h3 := entry_norm_bound_of_unitary ((Matrix.mem_unitaryGroup_iff' (A := u)).2 h1)
  have h4 : g = (M.fr τ)⁻¹ * u * M.fr τ := by
    rw [hu, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  have h5 : ‖⟪v, M.rep τ g a⟫_ℂ‖ ≤ ‖v‖ * ‖a‖ := by
    refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
    rw [DSModel.rep, (M.ds τ).2.2.1.2.1 u h2 a]
  have h6 : hsn g ≤ Real.sqrt (∑ i, ∑ j, (∑ l, (∑ k, ‖(M.fr τ)⁻¹ i k‖) * ‖M.fr τ l j‖) ^ 2) := by
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    conv_lhs => rw [h4]
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul, Matrix.mul_apply]
    refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (h3 k l)
  have h7 : 0 ≤ hsn g := Real.sqrt_nonneg _
  exact mul_le_mul h5 (pow_le_pow_left₀ (by linarith) (by linarith) N) (by positivity) (by positivity)

theorem exists_pack {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S : D.what₂.Tau → SPar} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) : ∃ p : Pack M₀ M, Adapted d p.A p.B ∧ p.g₀ ∈ GinfC V ∧
      (∀ τ, p.v₀ τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ∧ p.v₀ τ ≠ 0) ∧ ∀ τ, (p.w τ : M₀.H τ) ≠ 0 := by
  obtain ⟨B, hB⟩ := exists_adapted d (Fr.ofModel M₀) (Fr.ofModel M)
  choose v hv hv0 using fun τ => (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
  choose w hw hw0 using fun τ => (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D Y S' M₀ τ)
  exact ⟨⟨Fr.ofModel M₀, B, v, 1, fun τ => ⟨w τ, hw τ⟩⟩, hB, one_mem _, fun τ => ⟨hv τ, hv0 τ⟩, hw0⟩

theorem exists_base {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S : D.what₂.Tau → SPar} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) (hε : ∀ τ i, M.ε τ i = true) : ∃ p : Pack M₀ M, p.Base d ∧ KDecay M p.v₀ ∧ ∀ τ, p.v₀ τ ≠ 0 := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_pack d M₀ M
  exact ⟨p, ⟨h1, h2, fun τ => ⟨(h3 τ).1, decayAt_of_pos M τ (hε τ) _ _ _⟩, h4⟩,
    fun τ => ⟨(h3 τ).1, fun a _ => decayAt_of_pos M τ (hε τ) _ _ _⟩, fun τ => (h3 τ).2⟩

theorem v_ne_zero (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S : D.what₂.Tau → SPar} {S' : D.what₂.Tau → SPar}
    {M₀ : DSModel Y S'} {M : DSModel V S} (p : Pack M₀ M) (hb : p.Base d) {Q : ℝ} {m : Measure (GinfC Y)} {c : ℂ}
    (h : p.RealAt θ d Q m c) (τ : D.what₂.Tau) : p.v θ τ ≠ 0 := by
  intro h0
  have h1 := h.act fun τ => p.w τ
  have h2 : ∀ g, coefR θ M (p.v θ) (p.v θ) g = 0 := fun g =>
    Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [h0, inner_zero_left])
  simp only [h2, zero_mul, integral_zero] at h1
  exact mul_ne_zero h.ne (Finset.prod_ne_zero_iff.2 fun σ _ => inner_self_ne_zero.2 (hb.ne σ)) h1.symm

theorem exists_pays (D : D7) (Q : ℝ) : ∃ N, Pays D Q N := by
  set K : ℝ := Real.exp Q * ((D.R.r : ℝ) ^ 2 * Fintype.card D.what₂.Tau * (D.host.g 0 * D.host.g 1 : ℕ) * rdisc D) with hK
  have hK0 : 0 ≤ K := by unfold rdisc at hK; rw [hK]; positivity
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  set t : ℝ := 1 / (2 * (K + 1)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
  set s : ℝ := t ^ D.R.m / 2 with hs
  have hs0 : 0 < s := by positivity
  set R : ℝ := 2 * Real.exp (Q + (6 * ((D.R.r : ℝ) + 1) + 9) * Fintype.card D.what₂.Tau) with hR
  have hR0 : 0 < R := by positivity
  have e : s ^ Fintype.card D.what₂.Tau * Real.sqrt (((R + 2) / s ^ Fintype.card D.what₂.Tau) ^ 2) = R + 2 := by
    rw [Real.sqrt_sq (by positivity)]; field_simp
  refine ⟨((R + 2) / s ^ Fintype.card D.what₂.Tau) ^ 2, s, hs0, ?_, ?_, by rw [e]; linarith, by rw [e]; linarith⟩
  · have := pow_le_one₀ ht0.le ht1 (n := D.R.m); rw [hs]; linarith
  · have e2 : (2 * s) ^ ((1 : ℝ) / D.R.m) = t := by
      rw [hs, mul_div_cancel₀ _ (two_ne_zero), one_div, Real.pow_rpow_inv_natCast ht0.le hm]
    rw [e2, ← mul_assoc, ← hK, ht, mul_one_div, div_le_iff₀ (by positivity)]
    linarith

theorem not_pays_one (D : D7) (Q : ℝ) : ¬ Pays D Q 1 := by
  rintro ⟨s, h0, h1, -, -, h⟩
  have := pow_le_one₀ h0.le (by linarith : s ≤ 1) (n := Fintype.card D.what₂.Tau)
  simp at h; linarith

end GlobalTheory.SepPer.Model

end

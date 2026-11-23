import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

section rep

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rep_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lm : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : PI.UpqRep.IsDSHpk k r ε lm σ) :
    σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
      ∀ a ∈ UH (Hpk k r), ∀ v : H, ‖σ a v‖ = ‖v‖ := by
  obtain ⟨P, ⟨⟨_, hPJ⟩, hPU⟩, hDS⟩ := h
  obtain ⟨_, _, ⟨⟨h1, hmul⟩, hiso, _⟩, _⟩ := hDS
  have hsP : P.conjTranspose * P = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hPU
  have hPP : P * P.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hPU
  have hinv : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv hsP
  have conj : ∀ x : Mat k r, P⁻¹ * (P * x * P.conjTranspose) * P = x := by
    intro x
    rw [hinv]
    calc P.conjTranspose * (P * x * P.conjTranspose) * P = (P.conjTranspose * P) * x * (P.conjTranspose * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
  have hmem : ∀ a ∈ UH (Hpk k r), P * a * P.conjTranspose ∈ PI.UpqRep.UJset ε := by
    intro a ha
    have ha' : a.conjTranspose * Hpk k r * a = Hpk k r := ha
    show (P * a * P.conjTranspose).conjTranspose * PI.UpqRep.Jm ε * (P * a * P.conjTranspose) = PI.UpqRep.Jm ε
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P * (a.conjTranspose * P.conjTranspose) * PI.UpqRep.Jm ε * (P * a * P.conjTranspose)
        = P * (a.conjTranspose * (P.conjTranspose * PI.UpqRep.Jm ε * P) * a) * P.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = P * Hpk k r * P.conjTranspose := by rw [hPJ]; exact congrArg (fun m => P * m * P.conjTranspose) ha'
      _ = (P * P.conjTranspose) * PI.UpqRep.Jm ε * (P * P.conjTranspose) := by
        rw [show Hpk k r = P.conjTranspose * PI.UpqRep.Jm ε * P from hPJ.symm]; simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · have h1' : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hinv, hsP] at h1'
  · intro a ha b hb
    have e : P * a * P.conjTranspose * (P * b * P.conjTranspose) = P * (a * b) * P.conjTranspose := by
      calc P * a * P.conjTranspose * (P * b * P.conjTranspose) = P * a * (P.conjTranspose * P) * b * P.conjTranspose := by simp only [Matrix.mul_assoc]
        _ = P * (a * b) * P.conjTranspose := by rw [hsP, Matrix.mul_one, Matrix.mul_assoc P a b]
    have := hmul _ (hmem a ha) _ (hmem b hb)
    simp only [e, conj] at this
    exact this
  · intro a ha v
    have := hiso _ (hmem a ha) v
    simp only [conj] at this
    exact this

private theorem isUnit_det_of_mem_UH_Hpk' {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det := by
  have ha' : a.conjTranspose * Hpk k r * a = Hpk k r := ha
  have h1 : (a.conjTranspose * Hpk k r * a).det = (Hpk k r).det := by rw [ha']
  have h2 : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h1
  rw [← h1, zero_mul] at h2
  exact zero_ne_one h2

theorem inner_inv_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lm : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : PI.UpqRep.IsDSHpk k r ε lm σ) {a : Mat k r} (ha : a ∈ UH (Hpk k r)) (u w : H) :
    ⟪u, σ a⁻¹ w⟫_ℂ = ⟪σ a u, w⟫_ℂ := by
  obtain ⟨h1, hmul, hiso⟩ := rep_of_DS h
  have hinvm : a⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha
  have hc : σ a (σ a⁻¹ w) = w := by
    have := hmul a ha a⁻¹ hinvm
    rw [Matrix.mul_nonsing_inv a (isUnit_det_of_mem_UH_Hpk' ha), h1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]
    rfl
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ a : H →ₗ[ℂ] H), norm_map' := hiso a ha }
  calc ⟪u, σ a⁻¹ w⟫_ℂ = ⟪L u, L (σ a⁻¹ w)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪σ a u, w⟫_ℂ := by
      change ⟪σ a u, σ a (σ a⁻¹ w)⟫_ℂ = _
      rw [hc]

end rep

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem sum_basis_inner (T : Wq →L[ℂ] Wq) (ξ' : Wq) :
    ∑ i, star ⟪ξ', stdOrthonormalBasis ℂ Wq i⟫_ℂ * ⟪ξ', T (stdOrthonormalBasis ℂ Wq i)⟫_ℂ = ⟪ξ', T ξ'⟫_ℂ := by
  symm
  calc ⟪ξ', T ξ'⟫_ℂ = ⟪ξ', T (∑ i, ⟪stdOrthonormalBasis ℂ Wq i, ξ'⟫_ℂ • stdOrthonormalBasis ℂ Wq i)⟫_ℂ := by
        rw [(stdOrthonormalBasis ℂ Wq).sum_repr' ξ']
    _ = _ := by
      rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, inner_smul_right, ← inner_conj_symm (stdOrthonormalBasis ℂ Wq i) ξ']
      rfl

theorem hsInner_rank1 (T : Wq →L[ℂ] Wq) (U : Wp →L[ℂ] Wp) (α β : ℂ) (ξ : Wp) (ξ' : Wq) :
    hsInner (U.comp (((innerSL ℂ ξ').smulRight (α • ξ)).comp T)) ((innerSL ℂ ξ').smulRight (β • ξ)) =
      α * star β * ⟪ξ, U ξ⟫_ℂ * ⟪ξ', T ξ'⟫_ℂ := by
  rw [← sum_basis_inner T ξ']
  have e : ∀ x y : Wq, innerSL ℂ x y = ⟪x, y⟫_ℂ := fun _ _ => rfl
  simp only [hsInner, hsVec, PiLp.inner_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, e, map_smul, inner_smul_left, inner_smul_right,
    starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end hs

private theorem mul_mem_UH_Hpk_archimedean_coefficient_nonzero {k r : ℕ} {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  have ha' : a.conjTranspose * Hpk k r * a = Hpk k r := ha
  have hb' : b.conjTranspose * Hpk k r * b = Hpk k r := hb
  show (a * b).conjTranspose * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc b.conjTranspose * a.conjTranspose * Hpk k r * (a * b) = b.conjTranspose * (a.conjTranspose * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem aDil_mem_gv {k r : ℕ} {t : ℝ} (ht : 0 < t) : aDil k r t ∈ UH (Hpk k r) := by
  show (aDil k r t).conjTranspose * Hpk k r * aDil k r t = Hpk k r
  have hs : ∀ x : ℝ, star (x : ℂ) = x := fun x => Complex.conj_ofReal x
  ext i j
  unfold aDil
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  beta_reduce
  have hi := i.isLt
  have hj := j.isLt
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · have e : j.val - (r + k) = r - i.val := by omega
    have hj1 : ¬ j.val < r := by omega
    have hj2 : ¬ j.val ≤ r + k := by omega
    have hne : t ^ (r - i.val) ≠ 0 := pow_ne_zero _ ht.ne'
    rw [if_pos h1, if_pos h1.1, if_neg hj1, if_neg hj2, hs, e, mul_one, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hne, Complex.ofReal_one]
  · by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
    · have e : i.val - (r + k) = r - j.val := by omega
      have hi1 : ¬ i.val < r := by omega
      have hi2 : ¬ i.val ≤ r + k := by omega
      have hne : t ^ (r - j.val) ≠ 0 := pow_ne_zero _ ht.ne'
      rw [if_neg h1, if_pos h2, if_pos h2.1, if_neg hi1, if_neg hi2, hs, e, mul_one,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one]
    · by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
      · have hij : i = j := h3.2.2
        subst hij
        have hi1 : ¬ i.val < r := by omega
        rw [if_neg h1, if_neg h2, if_pos h3, if_neg hi1, if_pos h3.2.1]
        simp
      · rw [if_neg h1, if_neg h2, if_neg h3, mul_zero, zero_mul]

theorem phiAt_of (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) : PhiAt := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hlm hDS
  have hG := D.haarG
  haveI : IsFiniteMeasureOnCompacts D.μG := ⟨hG.finite_compact⟩
  have hHaar : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) D.μG :=
    ⟨inferInstance, hG.ne_zero, hG.conc, hG.left⟩
  obtain ⟨d, hd, hSch⟩ := hS k r ε lm H σ D.μG hlm hDS hHaar
  refine ⟨d, hd, ?_⟩
  intro v v' ξ ξ' p hp t ht1 ht2
  obtain ⟨h11, h12, h21, h22⟩ := hp
  obtain ⟨-, hmul, -⟩ := rep_of_DS hDS
  have hq12 : Matrix.of (conjM (aDil k r t.1) p.1.2) ∈ UH (Hpk k r) :=
    mul_mem_UH_Hpk_archimedean_coefficient_nonzero (mul_mem_UH_Hpk_archimedean_coefficient_nonzero (aDil_mem_gv ht1) h12.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (aDil_mem_gv ht1))
  have hq22 : Matrix.of (conjM (aDil k r t.2) p.2.2) ∈ UH (Hpk k r) :=
    mul_mem_UH_Hpk_archimedean_coefficient_nonzero (mul_mem_UH_Hpk_archimedean_coefficient_nonzero (aDil_mem_gv ht2) h22.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (aDil_mem_gv ht2))
  have hB : (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) ∈ UH (Hpk k r) := mul_mem_UH_Hpk_archimedean_coefficient_nonzero hq22 h21.1
  have hC : (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1) ∈ UH (Hpk k r) := mul_mem_UH_Hpk_archimedean_coefficient_nonzero hq12 h11.1
  have hCi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hC
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ UH (Hpk k r) := ae_iff.mpr hG.conc
  have key : ∀ᵐ g ∂D.μG, hsInner (rho D (dilation₂ t p) (coefM σ v v' ξ ξ') (Matrix.of g))
      (coefM σ v v' ξ ξ' (Matrix.of g)) =
      (⟪σ (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1) v, σ (Matrix.of g) (σ (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) v')⟫_ℂ * star ⟪v, σ (Matrix.of g) v'⟫_ℂ) *
        (⟪ξ, D.π (Matrix.of p.1.1) ξ⟫_ℂ * ⟪ξ', D.π' (Matrix.of p.2.1)⁻¹ ξ'⟫_ℂ) := by
    filter_upwards [hae] with g hg
    have e : (Matrix.of p.1.1)⁻¹ * (Matrix.of (conjM (aDil k r t.1) p.1.2))⁻¹ * Matrix.of g * Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1 =
        (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have hσ : σ ((Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1)) =
        (σ (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1)⁻¹).comp ((σ (Matrix.of g)).comp (σ (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1))) := by
      rw [hmul _ (mul_mem_UH_Hpk_archimedean_coefficient_nonzero hCi hg) _ hB, hmul _ hCi _ hg, ContinuousLinearMap.comp_assoc]
    change hsInner ((D.π (Matrix.of p.1.1)).comp (((innerSL ℂ ξ').smulRight
        (⟪v, σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of (conjM (aDil k r t.1) p.1.2))⁻¹ * Matrix.of g * Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) v'⟫_ℂ • ξ)).comp
        (D.π' (Matrix.of p.2.1)⁻¹))) ((innerSL ℂ ξ').smulRight (⟪v, σ (Matrix.of g) v'⟫_ℂ • ξ)) = _
    rw [hsInner_rank1, e, hσ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      inner_inv_of_DS hDS hC]
    ring
  unfold Ph
  rw [integral_congr_ae key, integral_mul_const, (hSch (σ (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) v') (σ (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1) v) v' v).2]
  simp only [Lf, Rf]
  ring

end PI.BICNZ

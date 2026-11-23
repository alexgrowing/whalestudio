import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousAdelicGL2Det

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Defs

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def nH (h : UpqT P Q) (X : Mat) : Mat := UpqT.mat h * ((1 + 1) + X) + ((1 + 1) - X)

def tauL (h : UpqT P Q) (X : lieU P Q) : lieU P Q := cayInv P Q (h * cayF P Q X)

def chA (h : UpqT P Q) (X : Mat) : Mat :=
  (4 : ℂ) • (((1 + 1) - X) * (nH h X)⁻¹ * UpqT.mat h * ((1 + 1) - X)⁻¹)

def chB (h : UpqT P Q) (X : Mat) : Mat := (4 : ℂ) • (nH h X)⁻¹

end Defs

def DetAYB : Prop := ∀ (P Q : ℕ) (A B : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
  (L : lieU P Q →ₗ[ℝ] lieU P Q),
  (∀ Y : lieU P Q, ((L Y : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
    A * (Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) * B) →
  |LinearMap.det L| = ‖A.det‖ ^ (P + Q) * ‖B.det‖ ^ (P + Q)

def TauDeriv : Prop := ∀ (P Q : ℕ) (h : UpqT P Q) (x : lieU P Q), x ∈ D0 P Q →
  IsUnit (nH h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).det →
  ∃ f' : lieU P Q →L[ℝ] lieU P Q,
    (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      chA h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
        (Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
          chB h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) ∧
    HasFDerivAt (tauL h) f' x

section Alg

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem mat_mul' (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem nH_eq (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q) :
    nH h (x : Mat) = (UpqT.mat (h * cayF P Q x) + 1) * ((1 + 1) - (x : Mat)) := by
  rw [mat_mul', add_mul, one_mul, mul_assoc, cayF_spec x hx]
  rfl

theorem nH_unit (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hu : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det) : IsUnit (nH h (x : Mat)).det := by
  rw [nH_eq h x hx, Matrix.det_mul]
  exact hu.mul hx

theorem tauL_val (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hu : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det) :
    ((tauL h x : lieU P Q) : Mat) =
      (1 + 1) - (4 : ℂ) • (((1 + 1) - (x : Mat)) * (nH h (x : Mat))⁻¹) := by
  have hrel := cayInv_rel (h * cayF P Q x) hu
  have hN := nH_eq h x hx
  have hA : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det := hu
  have hB : IsUnit ((1 + 1) - (x : Mat)).det := hx
  change UpqT.mat (h * cayF P Q x) * ((1 + 1) - ((tauL h x : lieU P Q) : Mat)) =
    (1 + 1) + ((tauL h x : lieU P Q) : Mat) at hrel
  have h4 : (4 : ℂ) • (1 : Mat) = (1 + 1) + (1 + 1) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  have hAτ : (UpqT.mat (h * cayF P Q x) + 1) * ((tauL h x : lieU P Q) : Mat) =
      (UpqT.mat (h * cayF P Q x) + 1) * (1 + 1) - (4 : ℂ) • (1 : Mat) := by
    have e : UpqT.mat (h * cayF P Q x) * ((tauL h x : lieU P Q) : Mat) =
        UpqT.mat (h * cayF P Q x) * (1 + 1) - ((1 + 1) + ((tauL h x : lieU P Q) : Mat)) := by
      rw [← hrel, mul_sub]
      abel
    rw [add_mul, one_mul, e, add_mul, one_mul, h4]
    abel
  have hτ : ((tauL h x : lieU P Q) : Mat) = (1 + 1) - (4 : ℂ) • (UpqT.mat (h * cayF P Q x) + 1)⁻¹ := by
    calc ((tauL h x : lieU P Q) : Mat)
        = (UpqT.mat (h * cayF P Q x) + 1)⁻¹ *
            ((UpqT.mat (h * cayF P Q x) + 1) * ((tauL h x : lieU P Q) : Mat)) := by
          rw [← mul_assoc, Matrix.nonsing_inv_mul _ hA, one_mul]
      _ = (UpqT.mat (h * cayF P Q x) + 1)⁻¹ *
            ((UpqT.mat (h * cayF P Q x) + 1) * (1 + 1) - (4 : ℂ) • (1 : Mat)) := by rw [hAτ]
      _ = (1 + 1) - (4 : ℂ) • (UpqT.mat (h * cayF P Q x) + 1)⁻¹ := by
          rw [mul_sub, ← mul_assoc, Matrix.nonsing_inv_mul _ hA, one_mul, Matrix.mul_smul, mul_one]
  have hinv : (UpqT.mat (h * cayF P Q x) + 1)⁻¹ = ((1 + 1) - (x : Mat)) * (nH h (x : Mat))⁻¹ := by
    rw [hN, Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ hB, one_mul]
  rw [hτ, hinv]

theorem card_PQ : Fintype.card (Fin P ⊕ Fin Q) = P + Q := by
  simp

theorem norm_det_mat (h : UpqT P Q) : ‖(UpqT.mat h).det‖ = 1 := by
  have hg : HcS.UG.cT (starRingEnd ℂ) (UpqT.mat h) * HcS.UG.Jpq P Q * UpqT.mat h = HcS.UG.Jpq P Q := h.2
  have hd := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hcT : (HcS.UG.cT (starRingEnd ℂ) (UpqT.mat h)).det = starRingEnd ℂ (UpqT.mat h).det := by
    unfold HcS.UG.cT
    rw [Matrix.det_transpose]
    exact (RingHom.map_det _ _).symm
  have hJ : (HcS.UG.Jpq P Q).det ≠ 0 := by
    unfold HcS.UG.Jpq
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  rw [hcT] at hd
  have h1 : starRingEnd ℂ (UpqT.mat h).det * (UpqT.mat h).det = 1 := by
    have h0 : (starRingEnd ℂ (UpqT.mat h).det * (UpqT.mat h).det - 1) * (HcS.UG.Jpq P Q).det = 0 := by
      linear_combination hd
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hJ
  have h3 : ‖(UpqT.mat h).det‖ ^ 2 = 1 := by
    have h2 := Complex.normSq_eq_conj_mul_self (z := (UpqT.mat h).det)
    rw [h1] at h2
    have h' : Complex.normSq (UpqT.mat h).det = 1 := by exact_mod_cast h2
    rwa [Complex.normSq_eq_norm_sq] at h'
  have h5 := norm_nonneg (UpqT.mat h).det
  exact le_antisymm (by nlinarith) (by nlinarith)

theorem dens_id (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hu : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det) (j : ℝ)
    (hj : |j| = ‖(chA h (x : Mat)).det‖ ^ (P + Q) * ‖(chB h (x : Mat)).det‖ ^ (P + Q)) :
    ENNReal.ofReal |j| * rhoH P Q (tauL h x) = rhoH P Q x := by
  have hB : IsUnit ((1 + 1) - (x : Mat)).det := hx
  have hN : IsUnit (nH h (x : Mat)).det := nH_unit h x hx hu
  have hcard : Fintype.card (Fin P ⊕ Fin Q) = P + Q := card_PQ
  have hmat := norm_det_mat h
  have hdA : (chA h (x : Mat)).det = (4 : ℂ) ^ (P + Q) * ((1 + 1) - (x : Mat)).det *
      ((nH h (x : Mat)).det)⁻¹ * (UpqT.mat h).det * (((1 + 1) - (x : Mat)).det)⁻¹ := by
    simp only [chA, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, hcard, Ring.inverse_eq_inv']
    ring
  have hdB : (chB h (x : Mat)).det = (4 : ℂ) ^ (P + Q) * ((nH h (x : Mat)).det)⁻¹ := by
    simp only [chB, Matrix.det_smul, Matrix.det_nonsing_inv, hcard, Ring.inverse_eq_inv']
  have hdτ : ((1 + 1) - ((tauL h x : lieU P Q) : Mat)).det =
      (4 : ℂ) ^ (P + Q) * ((1 + 1) - (x : Mat)).det * ((nH h (x : Mat)).det)⁻¹ := by
    rw [tauL_val h x hx hu, sub_sub_cancel, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, hcard,
      Ring.inverse_eq_inv']
    ring
  have ha : ‖((1 + 1) - (x : Mat)).det‖ ≠ 0 := norm_ne_zero_iff.2 hB.ne_zero
  have hn : ‖(nH h (x : Mat)).det‖ ≠ 0 := norm_ne_zero_iff.2 hN.ne_zero
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  have alg : ∀ (c a n : ℝ), c ≠ 0 → a ≠ 0 → n ≠ 0 → ∀ N : ℕ,
      (c * a * n⁻¹ * 1 * a⁻¹) ^ N * (c * n⁻¹) ^ N * ((c * a * n⁻¹)⁻¹) ^ (2 * N) = a⁻¹ ^ (2 * N) := by
    intro c a n hc ha hn N
    have e1 : c * a * n⁻¹ * 1 * a⁻¹ = c * n⁻¹ := by field_simp
    have e2 : (c * a * n⁻¹)⁻¹ = (c * n⁻¹)⁻¹ * a⁻¹ := by
      rw [show c * a * n⁻¹ = (c * n⁻¹) * a by ring, mul_inv]
    have hx : c * n⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hn)
    rw [e1, e2, ← pow_add, ← two_mul, mul_pow (c * n⁻¹)⁻¹ a⁻¹, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx,
      one_pow, one_mul]
  have key : (‖(chA h (x : Mat)).det‖ ^ (P + Q) * ‖(chB h (x : Mat)).det‖ ^ (P + Q)) *
      ‖((1 + 1) - ((tauL h x : lieU P Q) : Mat)).det‖⁻¹ ^ (2 * (P + Q)) =
      ‖((1 + 1) - (x : Mat)).det‖⁻¹ ^ (2 * (P + Q)) := by
    rw [hdA, hdB, hdτ]
    simp only [norm_mul, norm_pow, norm_inv, h4, hmat]
    exact alg _ _ _ (by positivity) ha hn _
  unfold rhoH
  rw [hj, ← ENNReal.ofReal_mul (by positivity), key]

end Alg

theorem huaInv_of (h1 : DetAYB) (h2 : TauDeriv) : HuaInv := by
  intro P Q lam hlam h S hSm hSD hhS
  have := hlam
  have hF := measurable_cayF (P := P) (Q := Q)
  have hD0m : MeasurableSet (D0 P Q) := isOpen_cell_domain.measurableSet
  have hbeta : ∀ T, MeasurableSet T →
      betaH P Q lam T = ∫⁻ x in cayF P Q ⁻¹' T ∩ D0 P Q, rhoH P Q x ∂lam := by
    intro T hT
    rw [betaH, Measure.map_apply hF hT, withDensity_apply _ (hF hT),
      Measure.restrict_restrict (hF hT)]
  have hhSm : MeasurableSet ((fun g => h * g) '' S) := by
    rw [Set.image_mul_left]
    exact (continuous_const.mul continuous_id).measurable hSm
  set s := cayF P Q ⁻¹' S ∩ D0 P Q with hs
  have hsm : MeasurableSet s := (hF hSm).inter hD0m
  have hmem : ∀ x ∈ s, IsUnit (UpqT.mat (h * cayF P Q x) + 1).det := by
    intro x hx
    have : h * cayF P Q x ∈ cayS (D0 P Q) := hhS ⟨cayF P Q x, hx.1, rfl⟩
    rw [cayley_domain_eq] at this
    exact this
  have hcay : ∀ x ∈ s, cayF P Q (tauL h x) = h * cayF P Q x := fun x hx =>
    cayF_eq_of _ _ (cayInv_rel _ (hmem x hx))
  have himg : cayF P Q ⁻¹' ((fun g => h * g) '' S) ∩ D0 P Q = tauL h '' s := by
    ext X'
    constructor
    · rintro ⟨⟨t, ht, hte⟩, hX'⟩
      obtain ⟨x, hxD, hxt⟩ := hSD ht
      have hcx : cayF P Q x = t := cayF_eq_of _ _ hxt
      refine ⟨x, ⟨by rw [Set.mem_preimage, hcx]; exact ht, hxD⟩, ?_⟩
      show cayInv P Q (h * cayF P Q x) = X'
      rw [hcx]
      rw [show h * t = cayF P Q X' from hte]
      exact cayInv_cayF X' hX'
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨cayF P Q x, hx.1, (hcay x hx).symm⟩, mem_cayley_domain_of _ _ (cayInv_rel _ (hmem x hx))⟩
  have hinj : Set.InjOn (tauL h) s := by
    intro x hx y hy hxy
    have e := hcay x hx
    rw [hxy, hcay y hy] at e
    have hc : cayF P Q x = cayF P Q y := (mul_left_cancel e).symm
    rw [← cayInv_cayF x hx.2, ← cayInv_cayF y hy.2, hc]
  have hderiv : ∀ x ∈ s, ∃ f' : lieU P Q →L[ℝ] lieU P Q,
      (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
        chA h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
          (Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
            chB h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) ∧
      HasFDerivAt (tauL h) f' x := fun x hx =>
    h2 P Q h x hx.2 (nH_unit h x hx.2 (hmem x hx))
  choose! f' hf'1 hf'2 using hderiv
  have : @BorelSpace (lieU P Q)
      (PseudoMetricSpace.toUniformSpace (α := lieU P Q)).toTopologicalSpace _ := ⟨rfl⟩
  have : @Measure.IsAddHaarMeasure (lieU P Q) _
      (PseudoMetricSpace.toUniformSpace (α := lieU P Q)).toTopologicalSpace _ lam := hlam
  rw [hbeta _ hhSm, hbeta _ hSm, himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul lam hsm
      (fun x hx => (hf'2 x hx).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hsm (fun x hx => ?_)
  exact dens_id h x hx.2 (hmem x hx) _ (h1 P Q _ _ (f' x : lieU P Q →ₗ[ℝ] lieU P Q) (hf'1 x hx))

end HcInf

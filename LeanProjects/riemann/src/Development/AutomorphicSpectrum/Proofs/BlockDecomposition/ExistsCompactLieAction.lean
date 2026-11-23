import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneParameterDifferentiable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp

noncomputable section

open Matrix Finset Filter Topology
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.DerivRep

variable {n : ℕ}

abbrev Mn (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

abbrev Un (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

def skw (Z : (Mn n)) : (Mn n) := (1 / 2 : ℂ) • (Z - Zᴴ)

theorem skw_skew (Z : (Mn n)) : (skw Z)ᴴ = -skw Z := by
  simp only [skw, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
  rw [← smul_neg, neg_sub]
  simp

theorem skw_of_skew {X : (Mn n)} (hX : Xᴴ = -X) : skw X = X := by
  rw [skw, hX, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
  norm_num

theorem skw_add (Z W : (Mn n)) : skw (Z + W) = skw Z + skw W := by
  simp only [skw, conjTranspose_add]
  module

theorem skw_real (s : ℝ) (Z : (Mn n)) : skw (s • Z) = (s : ℂ) • skw Z := by
  have e : s • Z = (s : ℂ) • Z := (Complex.coe_smul s Z).symm
  simp only [skw, e, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  module

theorem skw_I {X : (Mn n)} (hX : Xᴴ = -X) : skw (Complex.I • X) = 0 := by
  simp [skw, conjTranspose_smul, hX, Complex.star_def, Complex.conj_I]

theorem real_skew {X : (Mn n)} (hX : Xᴴ = -X) (s : ℝ) : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
  rw [conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]

theorem add_skew {X Y : (Mn n)} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) : (X + Y)ᴴ = -(X + Y) := by
  rw [conjTranspose_add, hX, hY, neg_add]

theorem bracket_skew {X Y : (Mn n)} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) : (X * Y - Y * X)ᴴ = -(X * Y - Y * X) := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX, hY]
  simp

theorem conj_skew (k : (Un n)) {X : (Mn n)} (hX : Xᴴ = -X) :
    ((k : (Mn n)) * X * star (k : (Mn n)))ᴴ = -((k : (Mn n)) * X * star (k : (Mn n))) := by
  rw [conjTranspose_mul, conjTranspose_mul, hX, star_eq_conjTranspose, conjTranspose_conjTranspose]
  simp [Matrix.mul_assoc]

theorem exp_mem {X : (Mn n)} (hX : Xᴴ = -X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, ← Matrix.exp_conjTranspose, real_skew hX,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • X)).neg_left, neg_add_cancel,
    NormedSpace.exp_zero]

def eU (X : (Mn n)) (hX : Xᴴ = -X) (t : ℝ) : (Un n) := ⟨NormedSpace.exp ((t : ℂ) • X), exp_mem hX t⟩

theorem eU_zero (X : (Mn n)) (hX : Xᴴ = -X) : eU X hX 0 = 1 :=
  Subtype.ext (by simp [eU, NormedSpace.exp_zero])

theorem eU_add (X : (Mn n)) (hX : Xᴴ = -X) (s t : ℝ) : eU X hX (s + t) = eU X hX s * eU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem eU_neg (X : (Mn n)) (hX : Xᴴ = -X) (s : ℝ) : (eU X hX s)⁻¹ = eU X hX (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← eU_add, add_neg_cancel, eU_zero])

theorem eU_continuous (X : (Mn n)) (hX : Xᴴ = -X) : Continuous (eU X hX) := by
  refine Continuous.subtype_mk ?_ _
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have hc : CompleteSpace (Mn n) := FiniteDimensional.complete ℝ _
  simp only [Complex.coe_smul]
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).continuousAt

section Rep

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  (ρ : (Un n) →* (H →L[ℂ] H))

def dA (X : (Mn n)) (hX : Xᴴ = -X) : H →L[ℂ] H := deriv (fun t : ℝ => ρ (eU X hX t)) 0

theorem dA_congr {X Y : (Mn n)} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (h : X = Y) : dA ρ X hX = dA ρ Y hY := by
  subst h
  rfl

variable {ρ}

theorem rho_exp (hρ : Continuous ρ) (X : (Mn n)) (hX : Xᴴ = -X) (t : ℝ) :
    ρ (eU X hX t) = NormedSpace.exp (t • dA ρ X hX) := by
  have h0 : (fun t : ℝ => ρ (eU X hX t)) 0 = 1 := by simp [eU_zero]
  obtain ⟨A, hA⟩ := Formalism.FourierDecayAlt.P.one_parameter_differentiable H (fun t : ℝ => ρ (eU X hX t)) h0
    (fun s t => by
      show ρ (eU X hX (s + t)) = _
      rw [eU_add, map_mul]
      rfl) (hρ.comp (eU_continuous X hX))
  have hAd : dA ρ X hX = A := by
    have h := (hA 0).deriv
    have h0' : ρ (eU X hX 0) = 1 := h0
    rw [h0'] at h
    exact h.trans (ContinuousLinearMap.id_comp A)
  rw [hAd]
  exact Formalism.FourierDecayAlt.P.GroupGeneratedByExp.group_eq_exp _ A h0 hA t

theorem dA_eq_of {X : (Mn n)} {hX : Xᴴ = -X} {B : H →L[ℂ] H}
    (h : ∀ t : ℝ, ρ (eU X hX t) = NormedSpace.exp (t • B)) : dA ρ X hX = B := by
  have : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) B (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  unfold dA
  rw [funext h]
  exact hd.deriv

theorem hasDeriv_dA (hρ : Continuous ρ) (X : (Mn n)) (hX : Xᴴ = -X) :
    HasDerivAt (fun t : ℝ => ρ (eU X hX t)) (dA ρ X hX) 0 := by
  have : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) (dA ρ X hX) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  rw [funext (rho_exp hρ X hX)]
  exact hd

theorem dA_smul (hρ : Continuous ρ) {X : (Mn n)} (hX : Xᴴ = -X) (s : ℝ) (h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X)) :
    dA ρ ((s : ℂ) • X) h = s • dA ρ X hX := by
  refine dA_eq_of fun t => ?_
  have e : eU ((s : ℂ) • X) h t = eU X hX (t * s) :=
    Subtype.ext (by simp only [eU, smul_smul, Complex.ofReal_mul])
  rw [e, rho_exp hρ, mul_smul]

theorem dA_add (hρ : Continuous ρ) {X Y : (Mn n)} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (h : (X + Y)ᴴ = -(X + Y)) :
    dA ρ (X + Y) h = dA ρ X hX + dA ρ Y hY := by
  have : CompleteSpace H := FiniteDimensional.complete ℂ H
  refine dA_eq_of fun t => ?_
  let u : ℕ → (Un n) := fun k => (eU X hX (((k : ℝ)⁻¹) * t) * eU Y hY (((k : ℝ)⁻¹) * t)) ^ k
  have hu : Tendsto u atTop (𝓝 (eU (X + Y) h t)) := by
    rw [tendsto_subtype_rng]
    have h1 := Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotterMx n ((t : ℂ) • X) ((t : ℂ) • Y)
    rw [← smul_add] at h1
    refine h1.congr fun k => ?_
    simp only [u, eU, smul_smul, Complex.ofReal_mul]
    rfl
  have h2 := (hρ.tendsto _).comp hu
  have h3 := Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotter (t • dA ρ X hX) (t • dA ρ Y hY)
  rw [← smul_add] at h3
  refine tendsto_nhds_unique h2 (h3.congr fun k => ?_)
  simp only [Function.comp, u, map_pow, map_mul, rho_exp hρ, smul_smul]

theorem dA_conj (hρ : Continuous ρ) (k : (Un n)) {X : (Mn n)} (hX : Xᴴ = -X)
    (h : ((k : (Mn n)) * X * star (k : (Mn n)))ᴴ = -((k : (Mn n)) * X * star (k : (Mn n)))) :
    dA ρ ((k : (Mn n)) * X * star (k : (Mn n))) h = ρ k * dA ρ X hX * ρ k⁻¹ := by
  have hd := hasDeriv_dA hρ X hX
  let L : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    (ContinuousLinearMap.compL ℂ H H H (ρ k)).comp ((ContinuousLinearMap.compL ℂ H H H).flip (ρ k⁻¹))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have h3 : (fun t : ℝ => ρ (eU ((k : (Mn n)) * X * star (k : (Mn n))) h t)) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => ρ (eU X hX t) := by
    funext t
    have e : eU ((k : (Mn n)) * X * star (k : (Mn n))) h t = k * eU X hX t * k⁻¹ := by
      apply Subtype.ext
      show NormedSpace.exp ((t : ℂ) • ((k : (Mn n)) * X * star (k : (Mn n)))) =
        (k : (Mn n)) * NormedSpace.exp ((t : ℂ) • X) * star (k : (Mn n))
      have hi : (k : (Mn n))⁻¹ = star (k : (Mn n)) := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 k.2)
      have hu : IsUnit (k : (Mn n)) := IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.1 k.2)
      rw [← hi, ← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
    rw [e, map_mul, map_mul]
    rfl
  unfold dA
  rw [h3]
  exact h2.deriv

theorem hasDeriv_apply (hρ : Continuous ρ) (X : (Mn n)) (hX : Xᴴ = -X) (w : H) :
    HasDerivAt (fun t : ℝ => ρ (eU X hX t) w) (dA ρ X hX w) 0 :=
  ((ContinuousLinearMap.apply ℂ H w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDeriv_dA hρ X hX)

def dB (hρ : Continuous ρ) : (Mn n) →ₗ[ℝ] (H →L[ℂ] H) where
  toFun Z := dA ρ (skw Z) (skw_skew Z)
  map_add' Z W := by
    rw [← dA_add hρ (skw_skew Z) (skw_skew W) (add_skew (skw_skew Z) (skw_skew W))]
    exact dA_congr ρ _ _ (skw_add Z W)
  map_smul' s Z := by
    simp only [RingHom.id_apply]
    rw [← dA_smul hρ (skw_skew Z) s (real_skew (skw_skew Z) s)]
    exact dA_congr ρ _ _ (skw_real s Z)

theorem dB_skew (hρ : Continuous ρ) {X : (Mn n)} (hX : Xᴴ = -X) : dB hρ X = dA ρ X hX :=
  dA_congr ρ _ _ (skw_of_skew hX)

theorem dB_I (hρ : Continuous ρ) {X : (Mn n)} (hX : Xᴴ = -X) : dB (ρ := ρ) hρ (Complex.I • X) = 0 := by
  show dA ρ (skw (Complex.I • X)) _ = 0
  have h0 := real_skew hX 0
  have e : skw (Complex.I • X) = ((0 : ℝ) : ℂ) • X := by rw [skw_I hX]; simp
  rw [dA_congr ρ _ h0 e, dA_smul hρ hX 0 h0, zero_smul]

def gL (hρ : Continuous ρ) : (Mn n) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun Z := dB hρ Z - Complex.I • dB hρ (Complex.I • Z)
  map_add' Z W := by
    simp only [smul_add, map_add]
    abel
  map_smul' c Z := by
    obtain ⟨r, s, rfl⟩ : ∃ r s : ℝ, c = r + s * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
    have e1 : ((r : ℂ) + s * Complex.I) • Z = r • Z + s • (Complex.I • Z) := by
      rw [← Complex.coe_smul r, ← Complex.coe_smul s]
      module
    have e2 : Complex.I • (((r : ℂ) + s * Complex.I) • Z) = r • (Complex.I • Z) + (-s) • Z := by
      rw [← Complex.coe_smul r, ← Complex.coe_smul (-s), smul_smul, smul_smul]
      have : Complex.I * ((r : ℂ) + s * Complex.I) = (r : ℂ) * Complex.I + ((-s : ℝ) : ℂ) := by
        push_cast
        linear_combination (s : ℂ) * Complex.I_sq
      rw [this, add_smul]
    simp only [RingHom.id_apply]
    rw [e2, e1]
    simp only [map_add, map_smul]
    simp only [← Complex.coe_smul]
    push_cast
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem gL_skew (hρ : Continuous ρ) {X : (Mn n)} (hX : Xᴴ = -X) : gL hρ X = dA ρ X hX := by
  show dB hρ X - Complex.I • dB hρ (Complex.I • X) = _
  rw [dB_I hρ hX, smul_zero, sub_zero, dB_skew hρ hX]

theorem ring_conj {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B * NormedSpace.exp (s • (-A))) (A * B - B * A) 0 := by
  have ha := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  have hb := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ)
  have h := (ha.mul_const B).mul hb
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg] at h
  rw [← sub_eq_add_neg] at h
  exact h

theorem lin_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : (Mn n) →ₗ[ℝ] E) (X Y : (Mn n)) :
    HasDerivAt (fun s : ℝ => L (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
      (L (X * Y - Y * X)) 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have hc : CompleteSpace (Mn n) := FiniteDimensional.complete ℝ _
  have h := ring_conj X Y
  have h1 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [Complex.coe_smul]
  exact h1

theorem dA_bracket (hρ : Continuous ρ) {X Y : (Mn n)} (hX : Xᴴ = -X) (hY : Yᴴ = -Y)
    (h : (X * Y - Y * X)ᴴ = -(X * Y - Y * X)) :
    dA ρ (X * Y - Y * X) h = dA ρ X hX * dA ρ Y hY - dA ρ Y hY * dA ρ X hX := by
  have : CompleteSpace H := FiniteDimensional.complete ℂ H
  have h1 := lin_conj (dB (ρ := ρ) hρ) X Y
  have h2 := ring_conj (dA ρ X hX) (dA ρ Y hY)
  have e : (fun s : ℝ => dB (ρ := ρ) hρ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))) =
      fun s : ℝ => NormedSpace.exp (s • dA ρ X hX) * dA ρ Y hY * NormedSpace.exp (s • (-dA ρ X hX)) := by
    funext s
    have hs : NormedSpace.exp ((s : ℂ) • (-X)) = star ((eU X hX s : (Un n)) : (Mn n)) := by
      have h3 : ((eU X hX s)⁻¹ : (Un n)).1 = star ((eU X hX s : (Un n)) : (Mn n)) := rfl
      rw [← h3, eU_neg]
      show _ = NormedSpace.exp (((-s : ℝ) : ℂ) • X)
      rw [Complex.ofReal_neg, neg_smul, smul_neg]
    have hk := conj_skew (eU X hX s) hY
    show dB hρ (((eU X hX s : (Un n)) : (Mn n)) * Y * NormedSpace.exp ((s : ℂ) • (-X))) = _
    rw [hs, dB_skew hρ hk, dA_conj hρ _ hY hk, eU_neg, rho_exp hρ, rho_exp hρ, smul_neg, neg_smul]
  rw [e] at h1
  rw [← dB_skew hρ h]
  exact h1.unique h2

theorem decomp (Z : (Mn n)) : ∃ P Q : (Mn n), Pᴴ = -P ∧ Qᴴ = -Q ∧ Z = P + Complex.I • Q := by
  refine ⟨skw Z, skw ((-Complex.I) • Z), skw_skew _, skw_skew _, ?_⟩
  simp only [skw, conjTranspose_smul, star_neg, Complex.star_def, Complex.conj_I, neg_neg]
  match_scalars <;> ring_nf <;> simp <;> norm_num

theorem expand {R : Type} [Ring R] [Algebra ℂ R] (P Q P' Q' : R) :
    (P + Complex.I • Q) * (P' + Complex.I • Q') - (P' + Complex.I • Q') * (P + Complex.I • Q) =
      (P * P' - P' * P) + Complex.I • (P * Q' - Q' * P) + Complex.I • (Q * P' - P' * Q) +
        (-1 : ℂ) • (Q * Q' - Q' * Q) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem gL_bracket (hρ : Continuous ρ) (Z W : (Mn n)) :
    gL (ρ := ρ) hρ (Z * W - W * Z) = gL hρ Z * gL hρ W - gL hρ W * gL hρ Z := by
  have key : ∀ {X Y : (Mn n)}, Xᴴ = -X → Yᴴ = -Y →
      gL (ρ := ρ) hρ (X * Y - Y * X) = gL hρ X * gL hρ Y - gL hρ Y * gL hρ X := by
    intro X Y hX hY
    rw [gL_skew hρ (bracket_skew hX hY), gL_skew hρ hX, gL_skew hρ hY, dA_bracket hρ hX hY]
  obtain ⟨P, Q, hP, hQ, rfl⟩ := decomp Z
  obtain ⟨P', Q', hP', hQ', rfl⟩ := decomp W
  have e1 : gL (ρ := ρ) hρ (P + Complex.I • Q) = gL hρ P + Complex.I • gL hρ Q := by rw [map_add, map_smul]
  have e2 : gL (ρ := ρ) hρ (P' + Complex.I • Q') = gL hρ P' + Complex.I • gL hρ Q' := by rw [map_add, map_smul]
  rw [expand P Q P' Q', e1, e2, expand (gL hρ P) (gL hρ Q) (gL hρ P') (gL hρ Q'), map_add, map_add, map_add,
    map_smul, map_smul, map_smul, key hP hP', key hP hQ', key hQ hP', key hQ hQ']

end Rep

section Inner

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {ρ : (Un n) →* (H →L[ℂ] H)}

theorem dA_skewAdj (hρ : Continuous ρ) (hiso : ∀ k v, ‖ρ k v‖ = ‖v‖) {X : (Mn n)} (hX : Xᴴ = -X) (x y : H) :
    ⟪dA ρ X hX x, y⟫_ℂ = -⟪x, dA ρ X hX y⟫_ℂ := by
  have h := (hasDeriv_apply hρ X hX x).inner ℂ (hasDeriv_apply hρ X hX y)
  have hc : (fun t : ℝ => ⟪ρ (eU X hX t) x, ρ (eU X hX t) y⟫_ℂ) = fun _ => ⟪x, y⟫_ℂ :=
    funext fun t => (LinearMap.norm_map_iff_inner_map_map (ρ (eU X hX t))).1 (hiso _) x y
  have h1 : HasDerivAt (fun t : ℝ => ⟪ρ (eU X hX t) x, ρ (eU X hX t) y⟫_ℂ)
      (⟪ρ (eU X hX 0) x, dA ρ X hX y⟫_ℂ + ⟪dA ρ X hX x, ρ (eU X hX 0) y⟫_ℂ) 0 := h
  rw [hc] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) ⟪x, y⟫_ℂ)
  rw [eU_zero, map_one] at h2
  simp only [ContinuousLinearMap.one_apply] at h2
  linear_combination h2

theorem gL_adj (hρ : Continuous ρ) (hiso : ∀ k v, ‖ρ k v‖ = ‖v‖) (Z : (Mn n)) (x y : H) :
    ⟪gL hρ Z x, y⟫_ℂ = ⟪x, gL hρ Zᴴ y⟫_ℂ := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := decomp Z
  have eH : (P + Complex.I • Q)ᴴ = (-1 : ℂ) • P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, hP, hQ, Complex.star_def, Complex.conj_I]
    simp
  rw [eH]
  simp only [map_add, map_smul, gL_skew hρ hP, gL_skew hρ hQ, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    dA_skewAdj hρ hiso hP x y, dA_skewAdj hρ hiso hQ x y, Complex.conj_I]
  ring

end Inner

theorem single_bracket (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 : (Mn n)) =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  have m : ∀ p q r s : Fin n, (Matrix.single p q (1 : ℂ) * Matrix.single r s 1 : (Mn n)) =
      if q = r then Matrix.single p s 1 else 0 := by
    intro p q r s
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, mul_one]
    · ext i j
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      simp only [Matrix.single_apply]
      split_ifs with h3 h4
      · exact absurd (h3.2.trans h4.1.symm) h
      all_goals simp
  rw [m, m]

theorem derivative_of_rep : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)), Continuous ρ → (∀ k v, ‖ρ k v‖ = ‖v‖) →
    ∃ G : Fin n → Fin n → Module.End ℂ H, Formalism.REAL.GlRel G ∧ (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) ∧
      (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
        (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
        HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) := by
  intro n H _ _ _ ρ hρ hiso
  let R := ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := H)
  refine ⟨fun a b => R (gL hρ (Matrix.single a b 1)), ?_, ?_, ?_⟩
  · intro a b c d
    have h := congrArg R (gL_bracket hρ (Matrix.single a b 1) (Matrix.single c d 1))
    rw [single_bracket] at h
    simp only [map_sub, map_mul] at h
    beta_reduce
    rw [← h]
    split_ifs <;> simp
  · intro a b x y
    have h := gL_adj hρ hiso (Matrix.single a b 1) x y
    rwa [Matrix.conjTranspose_single, star_one] at h
  · intro X γ hX hγ w
    obtain rfl : γ = eU X hX := funext fun t => Subtype.ext (hγ t)
    have hs : gL hρ X = ∑ a, ∑ b, X a b • gL hρ (Matrix.single a b 1) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    have e : (∑ a, ∑ b, X a b • R (gL hρ (Matrix.single a b 1)) w) = dA ρ X hX w := by
      rw [← gL_skew hρ hX, hs]
      simp [R, ContinuousLinearMap.sum_apply]
    simp only [e]
    exact hasDeriv_apply hρ X hX w

end GlobalTheory.CompanionTheory.RealCount.DerivRep

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem differentiable_mul_of_cr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G E : V → ℂ) (c : V → V → ℂ)
    (hG : Differentiable ℝ G) (hE : Differentiable ℝ E)
    (hGc : ∀ Z Y, fderiv ℝ G Z Y + Complex.I * fderiv ℝ G Z (Complex.I • Y) = -(c Z Y * G Z))
    (hEc : ∀ Z Y, fderiv ℝ E Z Y + Complex.I * fderiv ℝ E Z (Complex.I • Y) = c Z Y * E Z) :
    Differentiable ℂ (fun Z => G Z * E Z) := by
  intro Z
  have hL := (hG Z).hasFDerivAt.mul (hE Z).hasFDerivAt
  set L : V →L[ℝ] ℂ := G Z • fderiv ℝ E Z + E Z • fderiv ℝ G Z with hLdef
  have hI : ∀ Y, L (Complex.I • Y) = Complex.I * L Y := fun Y => by
    have h1 := hGc Z Y
    have h2 := hEc Z Y
    simp only [hLdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (-(Complex.I * E Z)) * h1 + (-(Complex.I * G Z)) * h2 +
      (E Z * fderiv ℝ G Z (Complex.I • Y) + G Z * fderiv ℝ E Z (Complex.I • Y)) * Complex.I_sq
  have hsm : ∀ (a : ℂ) (Y : V), L (a • Y) = a * L Y := fun a Y => by
    have e : a • Y = a.re • Y + a.im • (Complex.I • Y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im a).symm
    rw [e, L.map_add, L.map_smul, L.map_smul, hI, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im a]
    ring
  let g : V →L[ℂ] ℂ :=
    { toFun := fun Y => L Y
      map_add' := fun Y Y' => L.map_add Y Y'
      map_smul' := fun a Y => hsm a Y
      cont := L.continuous }
  exact (differentiableAt_iff_restrictScalars ℝ hL.differentiableAt).2 ⟨g, by rw [hL.fderiv]; ext Y; rfl⟩

theorem gauss_cr {ι : Type} [Fintype ι] {m n : ℕ} (r : ℝ) :
    Differentiable ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) ∧
    ∀ Z Y : ι → Fin m → Fin n → ℂ,
      fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z Y +
        Complex.I * fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z (Complex.I • Y) =
      (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) *
        Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) := by
  let P : ι → Fin m → Fin n → ((ι → Fin m → Fin n → ℂ) →L[ℝ] ℂ) := fun τ a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin m → Fin n → ℂ) τ))
  have hP : ∀ τ a b (Z : ι → Fin m → Fin n → ℂ), P τ a b Z = Z τ a b := fun _ _ _ _ => rfl
  have hq : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ => ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
      (∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b)) Z := fun Z => by
    refine HasFDerivAt.fun_sum fun τ _ => HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
    exact (P τ a b).hasFDerivAt.norm_sq
  have hE : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ))
      (Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * r) • ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b))) Z :=
    fun Z => (Complex.ofRealCLM.hasFDerivAt.comp Z ((hq Z).const_mul (Real.pi * r))).cexp
  refine ⟨fun Z => (hE Z).differentiableAt, fun Z Y => ?_⟩
  rw [(hE Z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply, hP, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, nsmul_eq_mul]
  have key : ∀ z y : ℂ, z * starRingEnd ℂ y =
      ((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ) := by
    intro z y
    rw [Complex.inner, Complex.inner]
    apply Complex.ext <;> simp <;> ring
  simp_rw [key]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem trace_frames {m n : ℕ} (GS B : Matrix (Fin n) (Fin n) ℂ) (GT B' : Matrix (Fin m) (Fin m) ℂ)
    (hB : Bᴴ * GS * B = 1) (hB' : B'ᴴ * GT * B' = 1) (Z Y : Matrix (Fin m) (Fin n) ℂ) :
    (GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹)).trace = ∑ a, ∑ b, Z a b * starRingEnd ℂ (Y a b) := by
  have e : GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹) = (GS⁻¹ * (B⁻¹)ᴴ) * (Yᴴ * Z) * B⁻¹ := by
    calc _ = GS⁻¹ * (B⁻¹)ᴴ * Yᴴ * (B'ᴴ * GT * B') * Z * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : B⁻¹ * (GS⁻¹ * (B⁻¹)ᴴ) = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hB, inv_one]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.FockPos

open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.FockPos

variable {D : D7}

def frLin {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank →L[ℂ] RW T S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ => (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ)
      map_add' := fun Y Z => by
        funext τ
        show (frAt frT τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = _ + _
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c Z => by
        funext τ
        show (frAt frT τ * (c • Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = c • _
        rw [Matrix.mul_smul, Matrix.smul_mul] }

theorem frLin_apply {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    frLin frS frT Z τ = (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) := rfl

theorem norm_embedding_xi0_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := by
  have hs : ∀ τ : D.host.E →+* ℂ, ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    intro τ
    have h0 : (τ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (τ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg, Complex.norm_natCast]
  unfold Formalism.L2.Pj.xiR Host.xi0
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, hs]

theorem xi_zero_eq_host (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) := by
  have h1 := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have h2 := Formalism.L2.Theta.xi_zero_im_pos D τ
  have h3 : ‖tauE D τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := norm_embedding_xi0_eq D (tauE D τ)
  have h4 : (tauE D τ D.host.xi0).im = Formalism.L2.Pj.xiR D := by
    rw [← h3, Complex.norm_def, Complex.normSq_apply, h1, zero_mul, zero_add, Real.sqrt_mul_self_eq_abs,
      abs_of_pos h2]
  apply Complex.ext <;> simp [h1, h4]

theorem vacuum_real_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f → ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  intro D ψ θ S T frS frT LS LT hS hT f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hf.1 S T (fun _ => 1) (fun _ => 1) f
    hf.2.theta hf.2.fock
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set X := frLin frS frT with hX
  set r := Formalism.L2.Pj.xiR D with hr
  set E : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hE
  have hU : ∀ {k : ℕ} (fr : GL (Fin k) D.host.E) τ, IsUnit (frAt fr τ).det := fun fr τ =>
    isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hG : Differentiable ℝ (fun Z => F (X Z)) := hF.comp (X.restrictScalars ℝ).differentiable
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (X Z)) Z Y = fderiv ℝ F (X Z) (X Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (X Z)) ((fderiv ℝ F (X Z)).comp (X.restrictScalars ℝ)) Z :=
      (hF (X Z)).hasFDerivAt.comp Z (X.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]
    rfl
  refine ⟨fun Z => F (X Z) * E Z,
    differentiable_mul_of_cr (fun Z => F (X Z)) E
      (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ))
      hG (gauss_cr r).1 (fun Z Y => ?_) (gauss_cr r).2, fun w hw => ?_⟩
  · rw [hdG, hdG]
    have hj : jO S T (fun _ => 1) (fun _ => 1) (X Y) = X (Complex.I • Y) := by
      rw [X.map_smul]
      funext τ
      rw [jO_apply]
      change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (X Y τ) *
        (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
      rw [Matrix.one_mul, Matrix.mul_one]
      rfl
    have h := hann (X Z) (X Y)
    rw [hj] at h
    have hom : ∀ Y' : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, omO S T (X Z) (X Y') =
        ∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y' τ a b)).re := by
      intro Y'
      rw [omO_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show 2 * (tauE D τ D.host.xi0 * hAt S T τ (X Z τ) (X Y' τ)).re = _
      unfold hAt
      rw [hX, frLin_apply, frLin_apply, trace_frames _ _ _ _ (frAt_on frS hS τ) (frAt_on frT hT τ), xi_zero_eq_host τ]
      rfl
    rw [hom, hom] at h
    have hs2 : ∀ τ, (∑ a, ∑ b, Z τ a b * starRingEnd ℂ ((Complex.I • Y) τ a b)) =
        -Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := fun τ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hs2] at h
    have key : ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) +
        Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) =
        2 * Complex.I * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set s := ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)
      apply Complex.ext <;> simp <;> ring
    show _ = -((2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) * F (X Z))
    have h' : fderiv ℝ F (X Z) (X Y) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) * F (X Z) +
      Complex.I * (fderiv ℝ F (X Z) (X (Complex.I • Y)) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) * F (X Z)) = 0 := h
    linear_combination h' + Real.pi * Complex.I * F (X Z) * key +
      2 * Real.pi * r * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)) * F (X Z) * Complex.I_sq
  · have e1 : X (zCo θ frS frT w) = piW θ T S w := by
      funext τ
      rw [hX, frLin_apply]
      change frAt frT τ * ((frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ) * (frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    show f w = gaussO θ frS frT w * (f (iotaW σ T S (X (zCo θ frS frT w))) * E (zCo θ frS frT w))
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, hE, gaussO, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hr]; push_cast; ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.FockPos

end

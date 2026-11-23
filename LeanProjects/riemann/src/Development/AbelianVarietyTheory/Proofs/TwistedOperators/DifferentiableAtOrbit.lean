import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DRepAddAndBracket

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.RealInd
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.GKLie

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem isUnit_Jm_det (ε : Fin n → Bool) : IsUnit (Jm ε).det :=
  isUnit_det_of_left_inverse (Jm_mul_self ε)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem dRep_add_bracket {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) {v : H} (hv : SmoothVec (lieSet ε) ρ v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hY : Y ∈ lieSet ε) :
    dRep ρ (X + Y) v = dRep ρ X v + dRep ρ Y v ∧
      dRep ρ (X * Y - Y * X) v = dRep ρ X (dRep ρ Y v) - dRep ρ Y (dRep ρ X v) := by
  set J := Jm ε with hJdef
  have hd : IsUnit J.det := isUnit_Jm_det ε
  have hJ : Jᴴ = J := Jm_conjTranspose ε
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X => J⁻¹ * Xᴴ * J
      map_add' := fun X Y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c X => by
        rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]; rfl }
  have hσ : ∀ Z, σ Z = J⁻¹ * Zᴴ * J := fun _ => rfl
  have hskew : ∀ Z, σ Z = -Z ↔ Zᴴ * J + J * Z = 0 := fun Z => by
    rw [hσ]
    constructor
    · intro h1
      rw [← mul_nonsing_inv_cancel_left _ (Zᴴ * J) hd, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
    · intro h1
      rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hd]
  have hun : ∀ u, σ u * u = 1 → u ∈ UJset ε := fun u h1 => by
    change uᴴ * J * u = J
    have := congrArg (J * ·) h1
    simpa only [hσ, ← mul_assoc, mul_nonsing_inv _ hd, one_mul, mul_one] using this
  refine GlobalTheory.DerivedAction.abstract σ (fun a b => ?_) ?_ (fun a => ?_) ρ hρ.1
    (fun a b ha hb => hρ.2 _ (hun a ha) _ (hun b hb)) v
    (fun k Xs h => hv k Xs fun i => (hskew _).1 (h i)) X ((hskew _).2 hX) Y ((hskew _).2 hY)
  · simp only [hσ, conjTranspose_mul, mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]
  · rw [hσ, conjTranspose_one, mul_one, nonsing_inv_mul _ hd]
  · rw [hσ, hσ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, mul_one]

theorem dRep_smul (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (r : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    dRep ρ (r • X) v = r • dRep ρ X v := by
  unfold dRep
  have : (fun t : ℝ => ρ (NormedSpace.exp (t • r • X)) v) =
      fun t : ℝ => (fun s : ℝ => ρ (NormedSpace.exp (s • X)) v) (r * t) := by
    funext t; rw [smul_smul, mul_comm]
  rw [this]
  have h := deriv_comp_mul_left r (fun s : ℝ => ρ (NormedSpace.exp (s • X)) v) 0
  simpa using h

theorem dRep_zero (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : dRep ρ 0 v = 0 := by
  simp [dRep]

theorem dsig_eq_dRep (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    PI.PhMeasCore.dsig ρ X v = dRep ρ X v := by
  unfold PI.PhMeasCore.dsig dRep
  congr 1
  try (funext t; rw [Complex.coe_smul])

theorem differentiableAt_orbit {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    (hv : SmoothVec (lieSet ε) ρ v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) :
    DifferentiableAt ℝ (fun t : ℝ => ρ (NormedSpace.exp (t • X)) v) 0 := by
  have h := (hv 1 (fun _ => X) fun _ => hX).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
  have := (h.differentiable (by simp)).differentiableAt (x := 0)
  simpa [Function.comp_def] using this

theorem dRep_add_vec {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v w : H}
    (hv : SmoothVec (lieSet ε) ρ v) (hw : SmoothVec (lieSet ε) ρ w) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) : dRep ρ X (v + w) = dRep ρ X v + dRep ρ X w := by
  unfold dRep
  simp_rw [map_add]
  exact deriv_add (differentiableAt_orbit hv hX) (differentiableAt_orbit hw hX)

theorem dRep_smul_vec {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    (hv : SmoothVec (lieSet ε) ρ v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) (c : ℂ) : dRep ρ X (c • v) = c • dRep ρ X v := by
  unfold dRep
  simp_rw [map_smul]
  exact deriv_const_smul c (differentiableAt_orbit hv hX)

section Theta

local notation "θ" => PI.DSInfCharCap.thetaJ ε

theorem theta_add (Y Z : Matrix (Fin n) (Fin n) ℂ) : θ (Y + Z) = θ Y + θ Z := by
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_add, mul_add, add_mul, neg_add]

theorem theta_smul (c : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) : θ (c • Y) = star c • θ Y := by
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_smul, mul_smul_comm, smul_mul_assoc, smul_neg]

theorem theta_neg (Y : Matrix (Fin n) (Fin n) ℂ) : θ (-Y) = -θ Y := by
  simp [PI.DSInfCharCap.thetaJ]

theorem theta_sub (Y Z : Matrix (Fin n) (Fin n) ℂ) : θ (Y - Z) = θ Y - θ Z := by
  rw [sub_eq_add_neg, theta_add, theta_neg, ← sub_eq_add_neg]

theorem theta_theta (Y : Matrix (Fin n) (Fin n) ℂ) : θ (θ Y) = Y := by
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose,
    Jm_conjTranspose, mul_neg, neg_mul, neg_neg, mul_assoc]
  rw [Jm_mul_self, mul_one, ← mul_assoc, Jm_mul_self, one_mul]

theorem theta_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : θ (X * Y) = -(θ Y * θ X) := by
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, neg_mul_neg, mul_assoc]
  rw [← mul_assoc (Jm ε) (Jm ε), Jm_mul_self, one_mul]

theorem mem_lieSet_iff (X : Matrix (Fin n) (Fin n) ℂ) : X ∈ lieSet ε ↔ θ X = X := by
  change Xᴴ * Jm ε + Jm ε * X = 0 ↔ _
  unfold PI.DSInfCharCap.thetaJ
  constructor
  · intro h
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h
    rw [mul_assoc, h1, mul_neg, ← mul_assoc, Jm_mul_self, one_mul, neg_neg]
  · intro h
    have h2 : Jm ε * X = -(Xᴴ * Jm ε) := by
      calc Jm ε * X = Jm ε * (-(Jm ε * Xᴴ * Jm ε)) := by rw [h]
        _ = -(Xᴴ * Jm ε) := by rw [mul_neg, ← mul_assoc, ← mul_assoc, Jm_mul_self, one_mul]
    rw [h2, add_neg_cancel]

theorem bracket_mem {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hY : Y ∈ lieSet ε) :
    X * Y - Y * X ∈ lieSet ε := by
  rw [mem_lieSet_iff] at *
  rw [theta_sub, theta_mul, theta_mul, hX, hY]
  abel

end Theta

def cre (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)

def cim (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)

theorem cre_mem (Y : Matrix (Fin n) (Fin n) ℂ) : cre ε Y ∈ lieSet ε := by
  rw [mem_lieSet_iff, cre, theta_smul, theta_add, theta_theta, add_comm (PI.DSInfCharCap.thetaJ ε Y)]
  congr 1
  simp

theorem cim_mem (Y : Matrix (Fin n) (Fin n) ℂ) : cim ε Y ∈ lieSet ε := by
  rw [mem_lieSet_iff, cim, theta_smul, theta_sub, theta_theta]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [this, neg_smul, ← smul_neg, neg_sub]

theorem cre_add_cim (Y : Matrix (Fin n) (Fin n) ℂ) : cre ε Y + Complex.I • cim ε Y = Y := by
  unfold cre cim
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [this]
  module

theorem cre_of_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) : cre ε X = X := by
  rw [mem_lieSet_iff] at hX
  rw [cre, hX, ← two_smul ℂ X, smul_smul]
  norm_num

theorem cim_of_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) : cim ε X = 0 := by
  rw [mem_lieSet_iff] at hX
  rw [cim, hX, sub_self, smul_zero]

theorem cre_add (Y Z : Matrix (Fin n) (Fin n) ℂ) : cre ε (Y + Z) = cre ε Y + cre ε Z := by
  unfold cre
  rw [theta_add]
  module

theorem cim_add (Y Z : Matrix (Fin n) (Fin n) ℂ) : cim ε (Y + Z) = cim ε Y + cim ε Z := by
  unfold cim
  rw [theta_add]
  module

theorem cre_ofReal (r : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : cre ε ((r : ℂ) • Y) = (r : ℂ) • cre ε Y := by
  unfold cre
  rw [theta_smul, Complex.star_def, Complex.conj_ofReal]
  module

theorem cim_ofReal (r : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : cim ε ((r : ℂ) • Y) = (r : ℂ) • cim ε Y := by
  unfold cim
  rw [theta_smul, Complex.star_def, Complex.conj_ofReal]
  module

theorem cre_I (Y : Matrix (Fin n) (Fin n) ℂ) : cre ε (Complex.I • Y) = -cim ε Y := by
  unfold cre cim
  rw [theta_smul, Complex.star_def, Complex.conj_I]
  have h : (1 / 2 : ℂ) * Complex.I = -(1 / (2 * Complex.I)) := by
    field_simp
    try rw [Complex.I_sq]
    try ring
  rw [smul_add, smul_smul, neg_smul, smul_neg, smul_smul, h, smul_sub]
  module

theorem cim_I (Y : Matrix (Fin n) (Fin n) ℂ) : cim ε (Complex.I • Y) = cre ε Y := by
  unfold cre cim
  rw [theta_smul, Complex.star_def, Complex.conj_I]
  have h : (1 / (2 * Complex.I)) * Complex.I = 1 / 2 := by
    field_simp
  rw [smul_sub, smul_smul, neg_smul, smul_neg, smul_smul, h, sub_neg_eq_add, smul_add]

theorem dsigC_eq (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    PI.DSInfCharCap.dsigC ε ρ Y v = dRep ρ (cre ε Y) v + Complex.I • dRep ρ (cim ε Y) v := by
  unfold PI.DSInfCharCap.dsigC
  rw [dsig_eq_dRep, dsig_eq_dRep]
  rfl

theorem dRep_neg (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    dRep ρ (-X) v = -dRep ρ X v := by
  rw [← neg_one_smul ℝ X, dRep_smul, neg_one_smul]

section Act

variable {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dsigC_add (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) {v : H} (hv : SmoothVec (lieSet ε) ρ v)
    (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.dsigC ε ρ (Y + Z) v = PI.DSInfCharCap.dsigC ε ρ Y v + PI.DSInfCharCap.dsigC ε ρ Z v := by
  rw [dsigC_eq, dsigC_eq, dsigC_eq, cre_add, cim_add, (dRep_add_bracket hρ hv (cre_mem Y) (cre_mem Z)).1,
    (dRep_add_bracket hρ hv (cim_mem Y) (cim_mem Z)).1, smul_add]
  abel

theorem dsigC_ofReal (r : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    PI.DSInfCharCap.dsigC ε ρ ((r : ℂ) • Y) v = (r : ℂ) • PI.DSInfCharCap.dsigC ε ρ Y v := by
  rw [dsigC_eq, dsigC_eq, cre_ofReal, cim_ofReal, Complex.coe_smul, Complex.coe_smul, dRep_smul, dRep_smul,
    Complex.coe_smul, smul_add, smul_comm r Complex.I]

theorem dsigC_I (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) :
    PI.DSInfCharCap.dsigC ε ρ (Complex.I • Y) v = Complex.I • PI.DSInfCharCap.dsigC ε ρ Y v := by
  rw [dsigC_eq, dsigC_eq, cre_I, cim_I, dRep_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem dsigC_smul (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) {v : H} (hv : SmoothVec (lieSet ε) ρ v)
    (c : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.dsigC ε ρ (c • Y) v = c • PI.DSInfCharCap.dsigC ε ρ Y v := by
  have hc : c • Y = (c.re : ℂ) • Y + (c.im : ℂ) • (Complex.I • Y) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, dsigC_add hρ hv, dsigC_ofReal, dsigC_ofReal, dsigC_I, smul_smul, ← add_smul, Complex.re_add_im]

theorem dsigC_add_vec {v w : H} (hv : SmoothVec (lieSet ε) ρ v) (hw : SmoothVec (lieSet ε) ρ w)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.dsigC ε ρ Y (v + w) = PI.DSInfCharCap.dsigC ε ρ Y v + PI.DSInfCharCap.dsigC ε ρ Y w := by
  rw [dsigC_eq, dsigC_eq, dsigC_eq, dRep_add_vec hv hw (cre_mem Y), dRep_add_vec hv hw (cim_mem Y), smul_add]
  abel

theorem dsigC_smul_vec {v : H} (hv : SmoothVec (lieSet ε) ρ v) (Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    PI.DSInfCharCap.dsigC ε ρ Y (c • v) = c • PI.DSInfCharCap.dsigC ε ρ Y v := by
  rw [dsigC_eq, dsigC_eq, dRep_smul_vec hv (cre_mem Y), dRep_smul_vec hv (cim_mem Y), smul_add,
    smul_comm c Complex.I]

theorem dsigC_mem (hV : IsGKSub ε ρ (kFinVec ε ρ)) (Y : Matrix (Fin n) (Fin n) ℂ) {v : H}
    (hv : v ∈ kFinVec ε ρ) : PI.DSInfCharCap.dsigC ε ρ Y v ∈ kFinVec ε ρ := by
  rw [dsigC_eq]
  exact add_mem (hV.lieStable _ (cre_mem Y) v hv) (Submodule.smul_mem _ _ (hV.lieStable _ (cim_mem Y) v hv))

def gAct (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε ρ) where
  toFun Y :=
    { toFun := fun v => ⟨PI.DSInfCharCap.dsigC ε ρ Y v, dsigC_mem hV Y v.2⟩
      map_add' := fun v w => Subtype.ext (dsigC_add_vec (hV.smooth v v.2) (hV.smooth w w.2) Y)
      map_smul' := fun c v => Subtype.ext (dsigC_smul_vec (hV.smooth v v.2) Y c) }
  map_add' Y Z := LinearMap.ext fun v => Subtype.ext (dsigC_add hρ (hV.smooth v v.2) Y Z)
  map_smul' c Y := LinearMap.ext fun v => Subtype.ext (dsigC_smul hρ (hV.smooth v v.2) c Y)

theorem gAct_coe (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : kFinVec ε ρ) :
    ((gAct hρ hV Y v : kFinVec ε ρ) : H) = PI.DSInfCharCap.dsigC ε ρ Y v := rfl

theorem gAct_of_mem (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (v : kFinVec ε ρ) :
    ((gAct hρ hV X v : kFinVec ε ρ) : H) = dRep ρ X v := by
  rw [gAct_coe, dsigC_eq, cre_of_mem hX, cim_of_mem hX, dRep_zero, smul_zero, add_zero]

theorem gAct_decomp (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    gAct hρ hV X = gAct hρ hV (cre ε X) + Complex.I • gAct hρ hV (cim ε X) := by
  conv_lhs => rw [← cre_add_cim (ε := ε) X]
  rw [map_add, map_smul]

theorem gAct_bracket_of_mem (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hY : Y ∈ lieSet ε) :
    gAct hρ hV (X * Y - Y * X) = gAct hρ hV X * gAct hρ hV Y - gAct hρ hV Y * gAct hρ hV X := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [gAct_of_mem hρ hV (bracket_mem hX hY), LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Submodule.coe_sub]
  simp only [gAct_of_mem hρ hV hX, gAct_of_mem hρ hV hY]
  exact (dRep_add_bracket hρ (hV.smooth v v.2) hX hY).2

theorem gAct_bracket (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    gAct hρ hV (X * Y - Y * X) = gAct hρ hV X * gAct hρ hV Y - gAct hρ hV Y * gAct hρ hV X := by
  have hm : ∀ X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ,
      (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
        (X1 * Y1 - Y1 * X1) + Complex.I • (X1 * Y2 - Y2 * X1) + Complex.I • (X2 * Y1 - Y1 * X2) -
          (X2 * Y2 - Y2 * X2) := by
    intro X1 X2 Y1 Y2
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul,
      smul_sub, smul_add, smul_neg, neg_smul, Complex.I_mul_I]
    module
  have h := hm (cre ε X) (cim ε X) (cre ε Y) (cim ε Y)
  rw [cre_add_cim, cre_add_cim] at h
  rw [h, map_sub, map_add, map_add, map_smul, map_smul, gAct_bracket_of_mem hρ hV (cre_mem X) (cre_mem Y),
    gAct_bracket_of_mem hρ hV (cre_mem X) (cim_mem Y), gAct_bracket_of_mem hρ hV (cim_mem X) (cre_mem Y),
    gAct_bracket_of_mem hρ hV (cim_mem X) (cim_mem Y), gAct_decomp hρ hV X, gAct_decomp hρ hV Y]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul,
    smul_sub, smul_add, smul_neg, neg_smul, Complex.I_mul_I]
  module

end Act

end GlobalTheory.GKLie

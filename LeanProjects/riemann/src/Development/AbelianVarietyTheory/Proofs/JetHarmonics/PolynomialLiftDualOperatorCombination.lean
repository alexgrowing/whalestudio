import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperatorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnitStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvecStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts

namespace GlobalTheory.HatNF.MirrorLift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open scoped ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_of_poly {N κ : ℕ} {φ : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ φ) : ContDiff ℝ ∞ φ := by
  obtain ⟨q, -, hq⟩ := h
  rw [show φ = _ from funext hq]
  clear hq
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    have he : ∀ a b : Fin N, ContDiff ℝ ∞ (fun g : Matrix (Fin N) (Fin N) ℂ => g a b) := fun a b =>
      (contDiff_apply_apply ℝ ℂ a b)
    rcases i with i | i
    · exact he _ _
    · exact Complex.conjCLE.contDiff.comp (he i.1 i.2)

theorem herm_poly {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (v w : Fin N → ℂ) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => herm H (g.mulVec v) w) := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec]
  refine PartialDerivativeAlgebra.pd_sum _ fun i _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 0 + 1 ≤ 1) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) ?_)
  refine PartialDerivativeAlgebra.pd_sum _ fun j _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 0 + 1 ≤ 1) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) ?_)
  exact PartialDerivativeAlgebra.pd_sum _ fun c _ => PartialDerivativeAlgebra.pd_mono (by norm_num : 1 + 0 ≤ 1) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_entry _ _) (PartialDerivativeAlgebra.pd_const _ 0))

theorem glRel_cast {A : Type*} [Ring A] {n n' : ℕ} (h : n = n') {E : Fin n' → Fin n' → A} (hE : GlRel E) :
    GlRel (fun a b => E (Fin.cast h a) (Fin.cast h b)) := by
  subst h; exact hE

theorem qminor_cast' {A : Type*} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (h : n = n') (E : Fin n' → Fin n' → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun a b => E (Fin.cast h a) (Fin.cast h b)) a b u = qminor E (Fin.cast h ∘ a) (Fin.cast h ∘ b) u := by
  subst h; rfl

theorem qdet_cast {A : Type*} [Ring A] [Algebra ℂ A] {n n' : ℕ} (h : n = n') (E : Fin n' → Fin n' → A) (u : ℂ) :
    qdet (fun a b => E (Fin.cast h a) (Fin.cast h b)) u = qminor E id id u := by
  subst h; rfl

section mul

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem good_mul (hD : IsOpen D) {φ : Q.Mx k r → ℂ} (hφ : ContDiffOn ℝ ∞ φ D) :
    Qx2.Good k r 0 D (fun (f : Q.Mx k r → E) g => φ g • f g) := by
  refine ⟨fun f hf g₀ hg₀ => ?_, fun f f₂ h x hx => by simp only [h x hx], fun f f₂ s _ _ x _ => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
    exact ⟨U ∩ D, fun x => φ x • F x, hU.inter hD, ⟨hgU, hg₀.2⟩,
      (hφ.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hG => by
        simp only [he x hx.1 hG]⟩
  · simp only [smul_add, smul_comm s]

def mulE (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) (φ : Q.Mx k r → ℂ) :
    Module.End ℂ (levData E 0 hD).V :=
  (levData E 0 hD).hat (fun f g => φ g • f g)

theorem mulE_apply (hD : IsOpen D) {φ : Q.Mx k r → ℂ} (hφ : ContDiffOn ℝ ∞ φ D) (F : (levData E 0 hD).V)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r 0 ∩ D) :
    ((mulE E hD φ F : (levData E 0 hD).V) : Q.Mx k r → E) g = φ g • (F : Q.Mx k r → E) g := by
  unfold mulE
  rw [HatData.hat_apply (good0 hD (good_mul hD hφ))]
  exact level_restriction_apply_on _ hg

theorem end_ext (hD : IsOpen D) {X Y : Module.End ℂ (levData E 0 hD).V}
    (h : ∀ F, ∀ g ∈ Q.Glev k r 0 ∩ D, (X F : Q.Mx k r → E) g = (Y F : Q.Mx k r → E) g) : X = Y := by
  refine LinearMap.ext fun F => Subtype.ext ?_
  rw [← (X F).2.2, ← (Y F).2.2]
  exact (level_restriction_eq_iff _ _).2 (h F)

theorem mulE_pow_apply (hD : IsOpen D) {φ : Q.Mx k r → ℂ} (hφ : ContDiffOn ℝ ∞ φ D) (s : ℕ) (F : (levData E 0 hD).V)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r 0 ∩ D) :
    (((mulE E hD φ ^ s) F : (levData E 0 hD).V) : Q.Mx k r → E) g = φ g ^ s • (F : Q.Mx k r → E) g := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ', Module.End.mul_apply, mulE_apply hD hφ _ hg, ih, smul_smul, pow_succ']

theorem mulE_prod_apply (hD : IsOpen D) : ∀ {p : ℕ} (φ : Fin p → Q.Mx k r → ℂ) (_ : ∀ j, ContDiffOn ℝ ∞ (φ j) D)
    (F : (levData E 0 hD).V) {g : Q.Mx k r} (_ : g ∈ Q.Glev k r 0 ∩ D),
    (((List.ofFn fun j => mulE E hD (φ j)).prod F : (levData E 0 hD).V) : Q.Mx k r → E) g =
      (∏ j, φ j g) • (F : Q.Mx k r → E) g
  | 0, φ, _, F, g, _ => by simp
  | p + 1, φ, hφ, F, g, hg => by
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, mulE_apply hD (hφ 0) _ hg,
      mulE_prod_apply hD (fun j => φ j.succ) (fun j => hφ j.succ) F hg, smul_smul, Fin.prod_univ_succ]

def evAt (hD : IsOpen D) (F : (levData E 0 hD).V) (g : Q.Mx k r) : Module.End ℂ (levData E 0 hD).V →ₗ[ℂ] E where
  toFun := fun X => (X F : Q.Mx k r → E) g
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem evAt_apply (hD : IsOpen D) (F : (levData E 0 hD).V) (g : Q.Mx k r) (X : Module.End ℂ (levData E 0 hD).V) :
    evAt hD F g X = (X F : Q.Mx k r → E) g := rfl

end mul

section group

variable {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)

theorem dim_eq (k r : ℕ) : r + 1 + (r + k) = Q.mdim k r 0 := by
  simp only [Q.mdim, Fin.val_zero]; omega

def pos (k r : ℕ) : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1) := finCongr (by omega)

theorem posL_cast (d : Fin (r + 1 + (r + k))) : Q.posL k r 0 (Fin.cast (dim_eq k r) d) = pos k r d := by
  apply Fin.ext; simp [Q.posL, pos]

def dZ (g : Q.Mx k r) : ℂ := (Zhat k r z z' g).det

def lam (g : Q.Mx k r) : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1)) ℂ :=
  fun a i => herm (Hpk k r) (g.mulVec (bvec (pos k r a))) (fvec k r z i)

theorem dZ_poly : U.IsPolyDeg (r + 1) (dZ z z') :=
  PartialDerivativeAlgebra.pd_det _ fun a b => zhat_pd k r z z' a b

theorem cramer_poly (a : Fin (r + 1 + (r + k))) (j : Fin (r + 1)) :
    U.IsPolyDeg (r + 1) (fun g => (Zhat k r z z' g).cramer (lam z g a) j) := by
  simp only [Matrix.cramer_apply]
  refine PartialDerivativeAlgebra.pd_det _ fun p q => ?_
  simp only [Matrix.updateCol_apply]
  split_ifs
  · exact herm_poly _ _ _
  · exact zhat_pd k r z z' p q

theorem isOpen_dom : IsOpen {g : Q.Mx k r | dZ z z' g ≠ 0} :=
  isOpen_ne_fun (contDiff_of_poly (dZ_poly z z')).continuous continuous_const

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def unitE (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin (r + 1 + (r + k))) :
    Module.End ℂ (levData E 0 (isOpen_dom z z')).V :=
  E0 E 0 (isOpen_dom z z') (Fin.cast (dim_eq k r) a) (Fin.cast (dim_eq k r) b)

theorem row_mul_det (q : Fin (r + 1 + (r + k)) → ℂ) (a : Fin (r + 1 + (r + k)))
    (F : (levData E 0 (isOpen_dom z z')).V) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r 0 ∩ {g | dZ z z' g ≠ 0}) :
    evAt (isOpen_dom z z') F g ((∑ d, q d • unitE z z' E a d) * mulE E (isOpen_dom z z') (dZ z z')) =
      dZ z z' g • evAt (isOpen_dom z z') F g (∑ d, q d • unitE z z' E a d) +
        (∑ j : Fin (r + 1), (∑ d, q d * fvec k r z' j (pos k r d)) * (Zhat k r z z' g).cramer (lam z g a) j) •
          (F : Q.Mx k r → E) g := by
  have hs : ContDiffOn ℝ ∞ (dZ z z') {g | dZ z z' g ≠ 0} := (contDiff_of_poly (dZ_poly z z')).contDiffOn
  have key : ∀ d, evAt (isOpen_dom z z') F g (unitE z z' E a d * mulE E (isOpen_dom z z') (dZ z z')) =
      dZ z z' g • evAt (isOpen_dom z z') F g (unitE z z' E a d) +
        (∑ j : Fin (r + 1), fvec k r z' j (pos k r d) * (Zhat k r z z' g).cramer (lam z g a) j) •
          (F : Q.Mx k r → E) g := by
    intro d
    rw [evAt_apply, evAt_apply, Module.End.mul_apply, unitE, level_generator_apply _ _ _ _ hg, level_generator_apply _ _ _ _ hg,
      (Qx2.good_eh (isOpen_dom z z') _ _).loc _ (fun x => (Zhat k r z z' x).det • (F : Q.Mx k r → E) x)
        (fun x hx => mulE_apply _ hs F hx) g hg,
      GlobalTheory.T.leibniz_det_frameMatrix_matrixUnit E k r z z' _ _ _ _ F.2.1 g hg]
    simp only [posL_cast]
    rfl
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc, map_sum, map_smul, key, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _
  · simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def coef (Qm : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ)
    (i : (Fin (r + k) → Fin (r + 1 + (r + k))) × (Fin (r + k) → Fin (r + 1 + (r + k)))) (g : Q.Mx k r) : ℂ :=
  Qm.det⁻¹ * ((Matrix.of fun a : Fin (r + 1 + (r + k)) =>
    Fin.append (lam z g a) (fun l : Fin (r + k) => if a = i.1 l then (1 : ℂ) else 0)).det *
      ((∏ l, Qm (Fin.natAdd (r + 1) l) (i.2 l)) * (((r + k).factorial : ℕ) : ℂ)⁻¹))

theorem coef_poly (Qm : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ) (i) :
    U.IsPolyDeg (r + 1 + (r + k)) (coef z Qm i) := by
  have h : U.IsPolyDeg (r + 1 + (r + k)) (fun g : Q.Mx k r => (Matrix.of fun a : Fin (r + 1 + (r + k)) =>
      Fin.append (lam z g a) (fun l : Fin (r + k) => if a = i.1 l then (1 : ℂ) else 0)).det) := by
    refine PartialDerivativeAlgebra.pd_det _ fun a b => ?_
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · simp only [Matrix.of_apply, Fin.append_left]
      exact herm_poly _ _ _
    · simp only [Matrix.of_apply, Fin.append_right]
      exact PartialDerivativeAlgebra.pd_const _ _
  exact PartialDerivativeAlgebra.pd_mono (by omega) (PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const _ 0) (PartialDerivativeAlgebra.pd_mul h (PartialDerivativeAlgebra.pd_const _ 0)))

theorem group_identity (hz' : inWb k r z') (hT : 0 < Tz k r z') (Y : ℂ) :
    ∃ (Qm : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ) (w : ℂ),
      ∀ (F : Q.Mx k r → E), B.CkOn ⊤ (B.GV k r) F → ∀ g ∈ B.GV k r, dZ z z' g ≠ 0 →
      ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
          (dZ z z' g ^ (r + 1 - (s : ℕ)) • Q.CV k r Y (fun x => dZ z z' x ^ (s : ℕ) • F x) g) =
        dZ z z' g ^ r • ∑ i : (Fin (r + k) → Fin (r + 1 + (r + k))) × (Fin (r + k) → Fin (r + 1 + (r + k))),
          coef z Qm i g • qminorOp (EabH (Hpk k r)) (pos k r ∘ i.1) (pos k r ∘ i.2) w F g := by
  obtain ⟨Qm, hQ, hQ1, hQ2⟩ := GlobalTheory.T.exists_dual_matrix_frame_fvec k r z' (pos k r) hz' hT
  set u := Q.uC k r 0 Y with hu
  refine ⟨Qm, u - ((r + 1 : ℕ) : ℂ), fun F hF g hgG hg0 => ?_⟩
  have hD := isOpen_dom z z'
  have hg : g ∈ Q.Glev k r 0 ∩ {g | dZ z z' g ≠ 0} := ⟨⟨hgG, fun a ha => absurd ha (by simp)⟩, hg0⟩
  have hFs : Q.SmoothLev k r 0 {g | dZ z z' g ≠ 0} F := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hF', he⟩ := hF g₀ hg₀.1.1
    exact ⟨U, F', hU, hgU, hF', fun x hx hG => he x hx hG.1⟩
  have hs : ContDiffOn ℝ ∞ (dZ z z') {g | dZ z z' g ≠ 0} := (contDiff_of_poly (dZ_poly z z')).contDiffOn
  set ν : Fin (r + 1 + (r + k)) → Fin (r + 1) → Q.Mx k r → ℂ :=
    fun a j x => (dZ z z' x)⁻¹ * (Zhat k r z z' x).cramer (lam z x a) j with hν
  have hνs : ∀ a j, ContDiffOn ℝ ∞ (ν a j) {g | dZ z z' g ≠ 0} := fun a j =>
    (hs.inv fun x hx => hx).mul (contDiff_of_poly (cramer_poly z z' a j)).contDiffOn
  have hGl : GlRel (unitE z z' E) := glRel_cast (dim_eq k r) (level_generators_gl_relations generator_gl_level 0 (isOpen_dom z z'))
  have top := GlobalTheory.T.capelliDet_conjugate_top_coefficient _ (r + 1) (r + k) (unitE z z' E) Qm (mulE E (isOpen_dom z z') (dZ z z'))
    (fun a j => mulE E (isOpen_dom z z') (ν a j)) u hGl
    (fun a j => end_ext _ fun G x hx => by
      have h := row_mul_det z z' (fun d => Qm (Fin.castAdd (r + k) j) d) a G hx
      rw [evAt_apply] at h
      rw [h, Module.End.mul_apply, mulE_apply _ hs _ hx, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
        mulE_apply _ (hνs a j) _ hx, smul_add, smul_smul]
      simp only [hQ1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hν]
      rw [mul_inv_cancel_left₀ hx.2]
      rfl)
    (fun a j => end_ext _ fun G x hx => by
      have h := row_mul_det z z' (fun d => Qm (Fin.natAdd (r + 1) j) d) a G hx
      rw [evAt_apply] at h
      rw [h, Module.End.mul_apply, mulE_apply _ hs _ hx]
      simp only [hQ2, zero_mul, Finset.sum_const_zero, zero_smul, add_zero]
      rfl)
    (fun a j => end_ext _ fun G x hx => by
      rw [Module.End.mul_apply, Module.End.mul_apply, mulE_apply _ hs _ hx, mulE_apply _ (hνs a j) _ hx,
        mulE_apply _ (hνs a j) _ hx, mulE_apply _ hs _ hx, smul_comm])
  have mnr := GlobalTheory.T.antisym_prod_eq_sum_quantumMinor _ (r + 1) (r + k) (unitE z z' E) (fun l d => Qm (Fin.natAdd (r + 1) l) d) (lam z g)
    ((Zhat k r z z' g)⁻¹).transpose (u - ((r + 1 : ℕ) : ℂ))
  set F0 := (levData E 0 (isOpen_dom z z')).toV F hFs with hF0
  have hF0v : ∀ x ∈ Q.Glev k r 0 ∩ {g | dZ z z' g ≠ 0}, (F0 : Q.Mx k r → E) x = F x := fun x hx => level_restriction_apply_on F hx
  have e1 := congrArg (evAt (isOpen_dom z z') F0 g) top
  have e2 := congrArg (evAt (isOpen_dom z z') F0 g) mnr
  have hU : IsUnit (Zhat k r z z' g).det := isUnit_iff_ne_zero.2 hg0
  have hLN : ∀ a j, (lam z g * ((Zhat k r z z' g)⁻¹).transpose) a j = ν a j g := by
    intro a j
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer (Zhat k r z z' g) (lam z g a) hU) j
    simp only [hν]
    rw [← this, Pi.smul_apply, smul_eq_mul, dZ, inv_mul_cancel_left₀ hU.ne_zero]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hL : ∀ s : ℕ, ∀ t : ℕ, evAt (isOpen_dom z z') F0 g (mulE E (isOpen_dom z z') (dZ z z') ^ t *
      (qdet (unitE z z' E) u * mulE E (isOpen_dom z z') (dZ z z') ^ s)) =
      dZ z z' g ^ t • Q.CV k r Y (fun x => dZ z z' x ^ s • F x) g := by
    intro s t
    rw [evAt_apply, Module.End.mul_apply, mulE_pow_apply _ hs _ _ hg, Module.End.mul_apply]
    congr 1
    have : qdet (unitE z z' E) u = qminor (E0 E 0 (isOpen_dom z z')) id id u := qdet_cast (dim_eq k r) _ u
    rw [this, quantum_minor_level_apply _ _ _ _ _ hg]
    exact (Qx2.good_qminor (isOpen_dom z z') id id u).loc _ _
      (fun x hx => by rw [mulE_pow_apply _ hs _ _ hx, hF0v x hx]) g hg
  have hR : ∀ c d : Fin (r + k) → Fin (r + 1 + (r + k)), ∀ w : ℂ,
      evAt (isOpen_dom z z') F0 g (qminor (unitE z z' E) c d w) =
        qminorOp (EabH (Hpk k r)) (pos k r ∘ c) (pos k r ∘ d) w F g := by
    intro c d w
    have : qminor (unitE z z' E) c d w = qminor (E0 E 0 (isOpen_dom z z')) (Fin.cast (dim_eq k r) ∘ c)
      (Fin.cast (dim_eq k r) ∘ d) w := qminor_cast' (dim_eq k r) _ c d w
    rw [evAt_apply, this, quantum_minor_level_apply _ _ _ _ _ hg,
      (Qx2.good_qminor (isOpen_dom z z') _ _ w).loc _ _ hF0v g hg]
    have hc : ∀ c : Fin (r + k) → Fin (r + 1 + (r + k)),
        Q.posL k r 0 ∘ Fin.cast (dim_eq k r) ∘ c = pos k r ∘ c := fun c => funext fun l => posL_cast _
    rw [hc, hc]
  have hM : ∀ (σ : Equiv.Perm (Fin (r + 1 + (r + k)))) (X : Module.End ℂ (levData E 0 (isOpen_dom z z')).V),
      evAt (isOpen_dom z z') F0 g ((List.ofFn fun j : Fin (r + 1) =>
        mulE E (isOpen_dom z z') (ν (σ (Fin.castAdd (r + k) j)) j)).prod * X) =
      (∏ j : Fin (r + 1), ν (σ (Fin.castAdd (r + k) j)) j g) • evAt (isOpen_dom z z') F0 g X := by
    intro σ X
    rw [evAt_apply, Module.End.mul_apply, mulE_prod_apply _ _ (fun j => hνs _ j) _ hg]
    rfl
  have hP : ∀ X : Module.End ℂ (levData E 0 (isOpen_dom z z')).V,
      evAt (isOpen_dom z z') F0 g (mulE E (isOpen_dom z z') (dZ z z') ^ (r + 1) * X) =
        dZ z z' g ^ (r + 1) • evAt (isOpen_dom z z') F0 g X := by
    intro X
    rw [evAt_apply, Module.End.mul_apply, mulE_pow_apply _ hs _ _ hg]
    rfl
  rw [hP] at e1
  simp only [map_smul, map_sum, hL, hM, hR, hLN] at e1 e2
  simp only [mul_smul] at e2
  rw [e2, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at e1
  rw [Fintype.sum_prod_type]
  simp only [coef, mul_smul, ← Finset.smul_sum]
  rw [eq_comm, ← inv_smul_eq_iff₀ hQ] at e1
  rw [← e1, smul_smul, smul_smul, smul_smul]
  congr 1
  have h0 : (Zhat k r z z' g).det ≠ 0 := hg0
  unfold dZ
  field_simp
  ring

end group

section radial

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem dZ_eq {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) :
    dZ z z' g = Dmin k r z z' g (Fin.last (r + 1)) := by
  unfold dZ Dmin
  congr 1

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem cpt_mul {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ∞ φ) : KB.CptCoef Bs (fun g => φ g • F g) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  refine ⟨fun g₀ hg₀ => ?_, ⟨R, fun g hg h => hR g hg fun h0 => h (by simp [h0])⟩,
    ⟨ε, hε, fun g hg h => hG g hg fun h0 => h (by simp [h0])⟩⟩
  obtain ⟨U, F', hU, hgU, hF', he⟩ := hs g₀ hg₀
  exact ⟨U, fun x => φ x • F' x, hU, hgU, hφ.contDiffOn.smul hF', fun x hx hG => by simp only [he x hx hG]⟩

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem cpt_congr {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F F₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    (h : ∀ g ∈ B.GV k r, F₂ g = F g) : KB.CptCoef Bs F₂ := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  refine ⟨fun g₀ hg₀ => ?_, ⟨R, fun g hg h' => hR g hg (h g hg ▸ h')⟩,
    ⟨ε, hε, fun g hg h' => hG g hg (h g hg ▸ h')⟩⟩
  obtain ⟨U, F', hU, hgU, hF', he⟩ := hs g₀ hg₀
  exact ⟨U, F', hU, hgU, hF', fun x hx hG => by rw [h x hG, he x hx hG]⟩

omit [FiniteDimensional ℂ Wp] in
theorem cpt_cap {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    (Y : ℂ) : KB.CptCoef Bs (Q.CV k r Y F) := by
  obtain ⟨Lw, hLw, hCV⟩ := capelli_word_sum k r Y
  have hLie : ∀ cw ∈ Lw, ∀ X ∈ cw.2, B.inLie k r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ Lw, cw.2.length ≤ 2 * r + k + 1 := fun cw h => (hLw cw h).2
  have hs : B.SmoothCoef (C6.domL Bs ∅) (TLB.capOp k r Wp Wq 1 Lw) := by
    intro T hT
    rcases List.mem_cons.1 hT with rfl | hT
    · exact (TLB.cTerm_inDDPlus Bs 0 _ _ (le_of_eq (List.length_replicate ..)) _ rfl).1
    · obtain ⟨cw, hcw, rfl⟩ := List.mem_map.1 hT
      exact (TLB.cTerm_inDDPlus Bs _ _ _ (hlen cw hcw) _ rfl).1
  refine cpt_congr ((compact_support_facts k r Wp Wq Bs F hF).2 _ hs).1 fun g hg => ?_
  rw [TLB.opApply_capOp 1 Lw hLie, hCV _ _ F (B5.ckOn_mono le_top hF.1) g hg hg, one_smul]

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem jf_mul_det {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (s : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => dZ Bs.z Bs.z' x ^ s • F x) g = dZ Bs.z Bs.z' g ^ s • B.JF Bs F g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => dZ Bs.z Bs.z' x ^ s • F x) g ∂Bs.μSS =
    dZ Bs.z Bs.z' g ^ s • ∫ p, JF.xiP Bs p • B.rho Bs p F g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [B5.ae_inSS Bs] with p hp
  simp only [B.rho, dZ_eq]
  rw [BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

theorem jf_sum {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {ι : Type} (s : Finset ι) (F : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ i, KB.CptCoef Bs (F i)) {g : B.Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    KB.CptCoef Bs (fun x => ∑ i ∈ s, F i x) ∧ B.JF Bs (fun x => ∑ i ∈ s, F i x) g = ∑ i ∈ s, B.JF Bs (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using PBN.cpt_zero' Bs, by simpa using JCx2.bc_JF_zero _⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine ⟨PBN.cpt_add Bs (hF a) ih.1, ?_⟩
    obtain ⟨ε₁, -, hn₁⟩ := TLB.nice_of_cpt (hF a)
    obtain ⟨ε₂, -, hn₂⟩ := TLB.nice_of_cpt ih.1
    rw [JCx2.bc_JF_add (TLB.nice_mono hn₁ (min_le_left ε₁ ε₂)) (TLB.nice_mono hn₂ (min_le_right ε₁ ε₂)) hg, ih.2]

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
  {μ : Measure (Mt P.k P.r)} {L : LevelData (RA P Bs) P.r} {st : Start (RA P Bs)} {l0 : ℕ}

theorem rad_cap (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (Y : ℂ)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (hΦ : Top.IsRadOf P Bs Φ F) :
    Top.IsRadOf P Bs ((P5.QQi L st 0 Y 0 0).1 Φ) (fun g => M.sgn P l0 • Q.CV P.k P.r Y F g) := by
  intro y hy
  set s : ℂ := M.sgn P l0 with hs
  obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hL := hD.2.2.1
  have hst := hD.2.2.2.1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  have hh := TLB.wCell_om Bs hy
  have h1 := JCx2.rma_QQi X L hL st s hst Y 0 0 Φ hy
  have h2 := (JCx2.rma_sandw X L hL Y P.r le_rfl _ _ (JCx2.rma_base X Y) (JCx2.rma_QL_loc Y)).2 0 0
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) (fun y' hy' => hΦ y' hy') y hy
  have h3 := chain_recursion_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) _ Y 0 0 hz hz'
    (JCx2.rma_isDom_omPlus hz hz') _ hJ y.1 hy.1 y.2 hy.2.1 hh.2
  rw [Fin.val_last] at h3
  have h4 : B.JF Bs (fun g => s • Q.CV P.k P.r Y F g) (Q.wCell P.k P.r (Fin.last P.r) y.1 * y.2) =
      s • Q.tL P.k P.r Bs.z Bs.z' 0 Y 0 0 (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) y.1 * y.2) :=
    (JCx2.bcGood_tL (Bs := Bs) (ε := ε) s Y 0 0).2.1 F hN _ hh
  refine Eq.trans h1 ?_
  rw [h2, ← h3]
  simp only [Q.resG]
  rw [h4, smul_comm]

theorem mulAt_pow {x : (Fin P.r → ℂ) × Q.Mx P.k P.r} {a : RA P Bs} {s : ℂ} (h : TLB.MulAt x a.1 s) :
    ∀ n : ℕ, TLB.MulAt x (a ^ n).1 (s ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact TLB.mulAt_one x
  | n + 1 => by rw [pow_succ, pow_succ]; exact TLB.mulAt_mul (mulAt_pow h n) h

theorem act_fns (hL : Q.IsActualLevel X L) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') :
    TLB.MulAt x L.Dr.1 (∏ a, x.1 a) ∧ TLB.MulAt x L.ζi.1 (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ ∧
    TLB.MulAt x L.D.1 (dZ Bs.z Bs.z' (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)) ∧
    TLB.MulAt x L.Di.1 (dZ Bs.z Bs.z' (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2))⁻¹ := by
  have hcell := big_cell_values P.k P.r Wp Wq Bs x hx
  have hDr : TLB.MulAt x L.Dr.1 (∏ a, x.1 a) := TLB.mulAt_ofFn L.c _ fun l => TLB.act_c X L hL x l
  have hDri : TLB.MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) := TLB.mulAt_ofFn L.ci _ fun l => TLB.act_ci X L hL x l
  have hz : TLB.MulAt x L.ζ.1 (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2) := by
    rw [hL.2.2.2.2.2.2.1]; exact TLB.act_fn X x hx 0
  have hzi : TLB.MulAt x L.ζi.1 (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ := by
    rw [hL.2.2.2.2.2.2.2.1]; exact TLB.act_fn X x hx 1
  refine ⟨hDr, hzi, ?_, ?_⟩
  · rw [dZ_eq, hcell.2.2.1]
    exact TLB.mulAt_mul hDr hz
  · rw [dZ_eq, hcell.2.2.1, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact TLB.mulAt_mul hzi hDri

theorem dZ_ne {g : B.Mat P.k P.r} (hg : g ∈ C6.domL Bs ∅) : dZ Bs.z Bs.z' g ≠ 0 := by
  intro h
  have := gram_function_last_minor P.k P.r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g _ le_rfl
  rw [← dZ_eq, h, map_zero] at this
  exact absurd hg.2.1 (not_lt.2 this)

theorem lift_regular {d : Q.NFData P (RA P Bs)} (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) (hd : IsNF X d)
    (y : ℝ) (h1 : (y : ℂ) ∈ st.inv) (h2 : (y : ℂ) - 1 ∈ st.inv) :
    PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rhv d y) := by
  have hy : star (y : ℂ) = y := Complex.conj_ofReal y
  obtain ⟨hA, hC, -⟩ := actual_algebra_facts Wp Wq P _ _ _ _ X μ L st l0 hD
  have hB := (TL.bFromCap _ P.r L st hA y hy h1 (Or.inl h2)).2
  have hL := hD.2.2.1
  have hdL := hd.1
  obtain ⟨Qm, w, hG⟩ := group_identity (E := Wq →L[ℂ] Wp) Bs.z Bs.z' Bs.z'_mem Bs.T'_pos (y : ℂ)
  obtain ⟨Θ, hΘ, hap⟩ := GlobalTheory.T.quantumMinor_sum_polynomialOperator Wp Wq P.k P.r (P.r + P.k) (P.r + 1 + (P.r + P.k)) _
    (fun i : (Fin (P.r + P.k) → Fin (P.r + 1 + (P.r + P.k))) × (Fin (P.r + P.k) → Fin (P.r + 1 + (P.r + P.k))) =>
      pos P.k P.r ∘ i.1) (fun i => pos P.k P.r ∘ i.2) w (fun i g => -coef Bs.z Qm i g)
    (fun i => by
      have := PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const (-1) 0) (coef_poly Bs.z Qm i)
      simpa using this)
  refine ⟨Θ, fun T hT => ?_, fun F hF Φ hΦ x hx => ?_⟩
  · obtain ⟨hl, φ, hφ, hc⟩ := hΘ T hT
    exact ⟨by omega, φ, PartialDerivativeAlgebra.pd_mono (by nlinarith) hφ, hc⟩
  have hT : L.Tvprod y = d.L.Tvprod y := by
    unfold LevelData.Tvprod
    congr 3
    funext l
    unfold LevelData.Tvl
    rw [hL.2.1 l, hdL.2.1 l, hL.2.2.2.2.1 l, hdL.2.2.2.2.1 l, hL.2.2.2.2.2.1 l, hdL.2.2.2.2.2.1 l]
  set s : ℂ := M.sgn P l0 with hs
  have hss : s * s = 1 := by rw [hs, M.sgn, ← mul_pow]; simp
  set W : RA P Bs := d.QQ y 0 1 * d.L.Avr y + d.QQ y 1 1 * d.L.Bvr y with hW
  have hbM : TL.bM L st y = L.ζi * (s • W) := by
    unfold TL.bM
    rw [hD.2.2.2.1, hd.2.2.2, hW]
    simp only [Matrix.smul_apply, smul_add, smul_mul_assoc, LevelData.Avr, LevelData.Bvr, hT]
    rfl
  set h := Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 with hh
  have hdom : h ∈ C6.domL Bs ∅ := PBN.cell_dom Bs hx
  have hD0 := dZ_ne hdom
  have hcell := (big_cell_values P.k P.r Wp Wq Bs x hx).2.2.1
  rw [← dZ_eq] at hcell
  have hζ : Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 ≠ 0 := fun h0 => hD0 (by rw [hh, hcell, h0, mul_zero])
  have hφ : ∀ t : ℕ, ContDiff ℝ ∞ fun g => dZ Bs.z Bs.z' g ^ t := fun t =>
    (contDiff_of_poly (dZ_poly Bs.z Bs.z')).pow t
  have e1 : ((rhv d y).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (s * dZ Bs.z Bs.z' h) • ((TL.bM L st y).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    have a1 := (act_fns hdL hx).1 (W.1 Φ)
    have a2 := (act_fns hL hx).2.1 ((s • W).1 Φ)
    have a3 : ((s • W).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = s • (W.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 :=
      rfl
    rw [hbM]
    refine a1.trans (Eq.symm ((congrArg _ a2).trans ?_))
    rw [a3, smul_smul, smul_smul, hh, hcell]
    congr 1
    calc _ = s * s * (∏ a, x.1 a) * (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 *
        (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹) := by ring
      _ = _ := by rw [hss, mul_inv_cancel₀ hζ, one_mul, mul_one]
  have e2 : ∀ t : ℕ, ((L.Di ^ t * TL.cst L st y * L.D ^ t).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (dZ Bs.z Bs.z' h)⁻¹ ^ t • s •
        Q.resG P.k P.r (Fin.last P.r) (B.JF Bs (Q.CV P.k P.r y fun g => dZ Bs.z Bs.z' g ^ t • F g)) x.1 x.2 := by
    intro t
    have r1 : Top.IsRadOf P Bs ((L.D ^ t).1 Φ) (fun g => dZ Bs.z Bs.z' g ^ t • F g) := by
      intro x' hx'
      rw [mulAt_pow (act_fns hL hx').2.2.1 t Φ, hΦ x' hx']
      simp only [Q.resG]
      rw [jf_mul_det, smul_comm]
    have r2 := rad_cap hD y (cpt_mul hF (hφ t)) r1 x hx
    rw [hC y hy] at r2
    refine (mulAt_pow (act_fns hL hx).2.2.2 t ((TL.cst L st y).1 ((L.D ^ t).1 Φ))).trans ?_
    rw [r2]
    simp only [Q.resG]
    rw [JCx2.bc_JF_smul, smul_comm s]
  have e3 : ((TL.bM L st y).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      -∑ t : Fin (P.r + 2), ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) t : ℝ) : ℂ) •
        ((L.Di ^ (t : ℕ) * TL.cst L st y * L.D ^ (t : ℕ)).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := by
    let ev : RA P Bs →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
      { toFun := fun a => (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have := congrArg ev hB
    rw [map_neg, map_sum] at this
    simp only [map_smul] at this
    exact this
  have e4 : dZ Bs.z Bs.z' h ^ P.r • B.JF Bs (B.opApply Θ F) h =
      -∑ t : Fin (P.r + 2), ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) t : ℝ) : ℂ) •
        (dZ Bs.z Bs.z' h ^ (P.r + 1 - (t : ℕ)) •
          B.JF Bs (Q.CV P.k P.r y fun g => dZ Bs.z Bs.z' g ^ (t : ℕ) • F g) h) := by
    have hj := (jf_sum Bs Finset.univ (fun (t : Fin (P.r + 2)) g =>
      ((F7.lagCo (fun j : Fin (P.r + 2) => ((j : ℕ) : ℝ)) t : ℝ) : ℂ) • (dZ Bs.z Bs.z' g ^ (P.r + 1 - (t : ℕ)) •
        Q.CV P.k P.r y (fun g => dZ Bs.z Bs.z' g ^ (t : ℕ) • F g) g))
      (fun t => PBN.cpt_smul Bs _ (cpt_mul (cpt_cap (cpt_mul hF (hφ t)) y) (hφ _))) (TLB.wCell_om Bs hx)).2
    simp only [JCx2.bc_JF_smul, jf_mul_det] at hj
    rw [← hj, ← jf_mul_det, ← neg_one_smul ℂ, ← JCx2.bc_JF_smul]
    refine PBN.jf_congr_pos Bs (fun g hg => ?_) hdom
    rw [hG F hF.1 g hg.1 (dZ_ne hg), hap F g hg.1 Set.univ isOpen_univ trivial (by rw [Set.inter_univ]; exact hF.1)]
    simp only [neg_smul, Finset.sum_neg_distrib, smul_neg, one_smul]
  rw [e1, e3]
  simp only [e2, Q.resG]
  rw [← hh, ← inv_smul_smul₀ (pow_ne_zero P.r hD0) (B.JF Bs (B.opApply Θ F) h), e4]
  simp only [smul_neg, Finset.smul_sum, smul_smul, neg_inj]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have ht : (t : ℕ) ≤ P.r + 1 := Nat.lt_succ_iff.1 t.isLt
  rw [pow_sub₀ _ hD0 ht, inv_pow, pow_succ]
  field_simp
  rw [pow_two, hss, one_mul]

end radial

theorem polyLift_rhv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rhv d y) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hd y
  let K : Submodule ℂ (RA P Bs) :=
    { carrier := {a | PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) a}
      zero_mem' := ⟨[], fun T hT => by simp at hT, TLB.radIs_zero P Bs⟩
      add_mem' := by
        rintro a b ⟨Θ₁, h₁, r₁⟩ ⟨Θ₂, h₂, r₂⟩
        refine ⟨Θ₁ ++ Θ₂, fun T hT => ?_, TLB.radIs_add P Bs ((polyOp_ok _ _ _ _ _ _ _ h₁).1 _)
          ((polyOp_ok _ _ _ _ _ _ _ h₂).1 _) r₁ r₂⟩
        rcases List.mem_append.1 hT with h | h
        · exact h₁ T h
        · exact h₂ T h
      smul_mem' := by
        rintro c a ⟨Θ, h, r⟩
        refine ⟨Θ.map (TLB.smulT c), fun T hT => ?_, TLB.radIs_smul P Bs c r⟩
        obtain ⟨T₀, h₀, rfl⟩ := List.mem_map.1 hT
        obtain ⟨hl, φ, hφ, hc, hc'⟩ := h T₀ h₀
        refine ⟨hl, fun g => c * φ g, by simpa using PartialDerivativeAlgebra.pd_mul (PartialDerivativeAlgebra.pd_const c 0) hφ, fun g => ?_, fun g => ?_⟩
        · show c • T₀.coef g = _
          rw [hc, smul_smul]
        · show (starRingEnd ℂ) c • T₀.coefAdj g = _
          rw [hc', smul_smul, star_mul']
          rfl }
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ (ρ : M.Ty P) (i : Finset.Icc 1 (P.k - 1)), -(M.rho P ρ i : ℝ) ≤ b := by
    obtain ⟨b, hb⟩ := (Set.finite_range fun x : M.Ty P × Finset.Icc 1 (P.k - 1) => -(M.rho P x.1 x.2 : ℝ)).bddAbove
    exact ⟨b, fun ρ i => hb ⟨(ρ, i), rfl⟩⟩
  have hinv : ∀ t : ℝ, b < t → (t : ℂ) ∈ st.inv := by
    intro t ht
    rw [hD.2.2.2.2.2.1]
    intro ρ
    unfold M.xC
    refine Finset.prod_ne_zero_iff.2 fun i hi h0 => ?_
    have h1 := hb ρ ⟨i, hi⟩
    have h2 : t + M.rho P ρ i = 0 := by exact_mod_cast h0
    simp only at h1
    linarith
  refine GlobalTheory.T.rightOperatorDual_mem_of_infinite P _ d K ((fun t : ℝ => (t : ℂ)) '' Set.Ioi (b + 1))
    ((Set.Ioi_infinite _).image Complex.ofReal_injective.injOn) ?_ y
  rintro _ ⟨t, ht, rfl⟩
  have ht' : b + 1 < t := ht
  refine lift_regular hD hd t (hinv t (by linarith)) ?_
  have := hinv (t - 1) (by linarith)
  rwa [Complex.ofReal_sub, Complex.ofReal_one] at this

end

end GlobalTheory.HatNF.MirrorLift

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracket
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList

noncomputable section

open Matrix GlobalTheory.TorFin GlobalTheory.SmoothForms
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.TorFin.RightRep

variable {n : ℕ} {G : Type} [Group G]

def sig (J : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := J⁻¹ * Xᴴ * J
  map_add' X Y := by rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := by
    change J⁻¹ * (c • X)ᴴ * J = c • (J⁻¹ * Xᴴ * J)
    rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

abbrev skewSub (J : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J).toSubmodule

theorem sig_mul_eq_one_iff {J : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit J.det) (u : Matrix (Fin n) (Fin n) ℂ) :
    sig J u * u = 1 ↔ IsUni J u := by
  change J⁻¹ * uᴴ * J * u = 1 ↔ uᴴ * J * u = J
  constructor
  · intro h1
    have := congrArg (J * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ hu, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc uᴴ, h1, nonsing_inv_mul _ hu]

theorem isLieData {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det) {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) : IsLieData (sig J) (skewSub J).subtype s := by
  have anti : ∀ a b, sig J (a * b) = sig J b * sig J a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hu]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun h => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change J⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J = 1
    rw [conjTranspose_one, mul_one, nonsing_inv_mul _ hu]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hu, nonsing_inv_mul _ hu, mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : J⁻¹ * Xᴴ * J = -X := h
    change Xᴴ * J + J * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J) hu, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J + J * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hu]
  · exact hs a b ((sig_mul_eq_one_iff hu a).1 ha) ((sig_mul_eq_one_iff hu b).1 hb)

theorem mem_smLoc_iff {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (hs : IsMulOn J s) (φ : G → ℂ) :
    φ ∈ smLoc J s ↔ Sm (expMap (skewSub J).subtype s) φ := by
  have H := isLieData hJ hu hs
  rw [SecondKind.sm_iff H (hasLog_of_isLieData _ _ _ _ _ _ H) Set.univ (by simp), mem_smLoc]
  constructor
  · intro h k Y _ g
    exact h k (fun i => (Y i).1) (fun i => (Y i).2) g
  · intro h k Z hZ g
    exact h k (fun i => ⟨Z i, hZ i⟩) (fun _ => trivial) g

variable {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hu : IsUnit J.det) {s : Matrix (Fin n) (Fin n) ℂ → G}
  (hs : IsMulOn J s)

def derL (X : skewSub J) : Module.End ℂ (smLoc J s) where
  toFun φ := ⟨Der (expMap (skewSub J).subtype s) X φ.1, (mem_smLoc_iff hJ hu hs _).2
    ((der_smooth_and_linear _ _ _ _ _ _ (isLieData hJ hu hs)
      (hasLog_of_isLieData _ _ _ _ _ _ (isLieData hJ hu hs)) φ.1 ((mem_smLoc_iff hJ hu hs _).1 φ.2)).1 X)⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add
    (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 φ.2) g X)
    (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 ψ.2) g X))
  map_smul' c φ := Subtype.ext (funext fun g =>
    deriv_const_smul c (Sm.differentiableAt ((mem_smLoc_iff hJ hu hs _).1 φ.2) g X))

theorem derL_apply (X : skewSub J) (φ : smLoc J s) :
    (derL hJ hu hs X φ).1 = Der (expMap (skewSub J).subtype s) X φ.1 := rfl

include hu hs in

theorem lineOf_add (Z : skewSub J) (t u : ℝ) : lineOf s Z.1 t * lineOf s Z.1 u = lineOf s Z.1 (t + u) := by
  have h1 : IsUni J (NormedSpace.exp (t • Z.1)) := exp_mem_UH hu (t • Z).2
  have h2 : IsUni J (NormedSpace.exp (u • Z.1)) := exp_mem_UH hu (u • Z).2
  unfold lineOf
  rw [← hs _ _ h1 h2, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Z.1).smul_left t).smul_right u)]

theorem hasDerivAt_derL (X : skewSub J) (φ : smLoc J s) (g : G) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => φ.1 (g * lineOf s X.1 τ)) ((derL hJ hu hs X φ).1 (g * lineOf s X.1 t)) t := by
  have hsm := (mem_smLoc_iff hJ hu hs _).1 φ.2
  set F : ℝ → ℂ := fun τ => φ.1 (g * lineOf s X.1 τ) with hFdef
  have hF : Differentiable ℝ F :=
    ((hsm g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun τ : ℝ => τ • X)).differentiable (by simp)
  have key : (fun u : ℝ => φ.1 (g * lineOf s X.1 t * expMap (skewSub J).subtype s (u • X))) =
      fun u => F (t + u) := funext fun u => by
    show φ.1 (g * lineOf s X.1 t * lineOf s X.1 u) = φ.1 (g * lineOf s X.1 (t + u))
    rw [mul_assoc, lineOf_add hu hs]
  have e : (derL hJ hu hs X φ).1 (g * lineOf s X.1 t) = deriv F t := by
    rw [derL_apply]
    show deriv (fun u : ℝ => φ.1 (g * lineOf s X.1 t * expMap (skewSub J).subtype s (u • X))) 0 = _
    rw [key, deriv_comp_const_add, add_zero]
  rw [e]
  exact (hF t).hasDerivAt

end GlobalTheory.TorFin.RightRep

namespace GlobalTheory.TorFin

open RightRep in

theorem exists_rightDer_rep : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ)
    (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s →
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsLieRep ρ ∧ IsRightDer J s ρ := by
  intro n G _ J s hJ hu hs
  have H := isLieData hJ hu hs
  have hl := hasLog_of_isLieData _ _ _ _ _ _ H
  let ρ₀ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → Module.End ℂ (smLoc J s) := fun X => derL hJ hu hs ⟨X.1, X.2⟩
  have hsm : ∀ φ : smLoc J s, Sm (expMap (skewSub J).subtype s) φ.1 := fun φ => (mem_smLoc_iff hJ hu hs _).1 φ.2
  obtain ⟨R, -, hR, hc⟩ := GlobalTheory.UnitaryLieComplexification.exists_extension hJ hu ρ₀
    (fun X Y => LinearMap.ext fun φ => Subtype.ext
      ((der_smooth_and_linear _ _ _ _ _ _ H hl φ.1 (hsm φ)).2.1 ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩))
    (fun c X => LinearMap.ext fun φ => Subtype.ext
      ((der_smooth_and_linear _ _ _ _ _ _ H hl φ.1 (hsm φ)).2.2 c ⟨X.1, X.2⟩))
    (fun X Y Z hZ => LinearMap.ext fun φ => Subtype.ext
      (Bracket.der_bracket _ _ _ _ _ _ H hl φ.1 (hsm φ) ⟨X.1, X.2⟩ ⟨Y.1, Y.2⟩ ⟨Z.1, Z.2⟩ hZ).symm)
  refine ⟨R, hc, fun Z hZ φ g t => ?_⟩
  have hRZ : R Z = derL hJ hu hs ⟨Z, hZ⟩ := hR ⟨Z, hZ⟩
  rw [hRZ]
  exact hasDerivAt_derL hJ hu hs ⟨Z, hZ⟩ φ g t

end GlobalTheory.TorFin

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame

noncomputable section

namespace GlobalTheory.TorusFrame

open NumberField Matrix Complex GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem angles_add (φ ψ : Fin (r - 1) → ℝ) (a : Fin r) : angles (φ + ψ) a = angles φ a + angles ψ a := by
  unfold angles; split_ifs <;> simp [Finset.sum_add_distrib]; ring

theorem angles_smul (c : ℝ) (φ : Fin (r - 1) → ℝ) (a : Fin r) : angles (c • φ) a = c * angles φ a := by
  unfold angles; split_ifs <;> simp [Finset.mul_sum]

theorem angles_zero (a : Fin r) : angles (0 : Fin (r - 1) → ℝ) a = 0 := by
  unfold angles; split_ifs <;> simp

def anglesL (r : ℕ) : (Fin (r - 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun φ a := angles φ a
  map_add' φ ψ := funext fun a => angles_add φ ψ a
  map_smul' c φ := funext fun a => angles_smul c φ a

theorem continuous_angles (a : Fin r) : Continuous fun φ : Fin (r - 1) → ℝ => angles φ a :=
  ((continuous_apply a).comp (LinearMap.continuous_of_finiteDimensional (anglesL r)) :)

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isUnit_det_of_isOrth {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    IsUnit (mat x τ).det := by
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq, det_mul, det_mul, det_transpose, det_diagonal] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_mul, zero_mul] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn; split_ifs <;> norm_num

def frameU {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : GL (Fin r) ℂ :=
  nonsingInvUnit (mat x τ) (isUnit_det_of_isOrth hx τ)

def phaseU (φ : Fin (r - 1) → ℝ) : GL (Fin r) ℂ where
  val := diagonal fun a => exp (I * (angles φ a : ℂ))
  inv := diagonal fun a => exp (-(I * (angles φ a : ℂ)))
  val_inv := by rw [diagonal_mul_diagonal]; simp [← exp_add]
  inv_val := by rw [diagonal_mul_diagonal]; simp [← exp_add]

def torusGL {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => frameU hx τ * phaseU (θ τ) * (frameU hx τ)⁻¹

theorem torusGL_val {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) (τ : X.Ψ) :
    ((torusGL hx θ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => exp (I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ := rfl

def torusDerL {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun θ τ a b := (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b
  map_add' θ θ' := by
    funext τ a b
    simp only [Pi.add_apply, angles_add, ofReal_add, mul_add, ← diagonal_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c θ := by
    funext τ a b
    have : (diagonal fun d => I * (angles (c • θ τ) d : ℂ)) = (c : ℂ) • diagonal fun d => I * (angles (θ τ) d : ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, angles_smul]; ring
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

def torusDer {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →L[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
  LinearMap.toContinuousLinearMap (torusDerL x)

theorem torusDer_apply {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (θ : Ψ → Fin (r - 1) → ℝ) (τ : Ψ) (a b : Fin r) :
    torusDer x θ τ a b = (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b := rfl

end GlobalTheory.TorusFrame

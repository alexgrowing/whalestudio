import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.SiegelTorusMat

theorem eq_of_scales {n q : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin q) ℂ}
    {P Q : Matrix (Fin q) (Fin n) ℂ} {d e : Fin q → ℂ} (hX : A * X = X * Matrix.diagonal d)
    (hY : A * Y = Y * Matrix.diagonal e) (hZ : A * (1 - X * P - Y * Q) = 1 - X * P - Y * Q) :
    A = 1 + X * Matrix.diagonal (fun i => d i - 1) * P + Y * Matrix.diagonal (fun i => e i - 1) * Q := by
  have h : ∀ a : Fin q → ℂ, Matrix.diagonal (fun i => a i - 1) = Matrix.diagonal a - 1 := fun a => by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, Matrix.mul_one,
    sub_sub, sub_eq_iff_eq_add] at hZ
  rw [h, h, hZ]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem inv_scales {n q : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) {X : Matrix (Fin n) (Fin q) ℂ}
    {d e : Fin q → ℂ} (hde : ∀ i, d i * e i = 1) (hX : A * X = X * Matrix.diagonal d) :
    B * X = X * Matrix.diagonal e := by
  have h : X * Matrix.diagonal d * Matrix.diagonal e = X := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [hde, Matrix.diagonal_one, Matrix.mul_one]
  conv_lhs => rw [← h, ← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem archMat_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E), GlobalTheory.SiegelSet.IsWittFrame σ J Xf Yf →
    ∀ (t : Fin q → ℝ), (∀ i, 0 < t i) → ∀ a : GAd σ J, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
      GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
                   (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) := by
  intro F E _ _ _ _ _ σ h n J hJ q X Y hW t ht a ha w τ
  have cc : ∀ Z : Matrix (Fin n) (Fin q) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun i j => GlobalTheory.SiegelSet.sigma_sigma h _
  have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have xx := hW.xx
  have yy := hW.yy
  have xy := hW.xy
  obtain ⟨hX, hY, hz⟩ := ha.2 w τ
  generalize Formalism.UG.cT (σ : E →+* E) Y * J = P at *
  generalize Formalism.UG.cT (σ : E →+* E) X * J = Q at *
  have hBA : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = A at *
  generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = B at *
  have hQ : Q * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  have hP : P * (1 - X * P - Y * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp
  have hZ0 : A * (1 - X * P - Y * Q).map τ.1 = (1 - X * P - Y * Q).map τ.1 := by
    generalize (1 - X * P - Y * Q) = Z at *
    ext i j
    exact congrFun (hz (fun k => Z k j) (funext fun k => congrFun (congrFun hQ k) j)
      (funext fun k => congrFun (congrFun hP k) j)) i
  have hm : (1 - X * P - Y * Q).map τ.1 = 1 - X.map τ.1 * P.map τ.1 - Y.map τ.1 * Q.map τ.1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← RingHom.mapMatrix_apply, map_sub, map_sub, map_one]
    rfl
  rw [hm] at hZ0
  have ht' : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  refine ⟨eq_of_scales hX hY hZ0, eq_of_scales (inv_scales hBA (fun i => ?_) hX) (inv_scales hBA (fun i => ?_) hY) ?_⟩
  · rw [Complex.ofReal_inv, mul_inv_cancel₀ (ht' i)]
  · rw [Complex.ofReal_inv, inv_inv, inv_mul_cancel₀ (ht' i)]
  · conv_lhs => rw [← hZ0, ← Matrix.mul_assoc, hBA, Matrix.one_mul]

end GlobalTheory.SiegelTorusMat

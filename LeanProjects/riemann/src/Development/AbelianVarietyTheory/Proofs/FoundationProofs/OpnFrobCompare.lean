import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EnvOfMat
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix

noncomputable section

namespace GlobalTheory.SOrb.CCBridge

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

lemma lin_bound {𝕜 L M : Type*} [RCLike 𝕜] [NormedAddCommGroup L] [NormedSpace 𝕜 L] [FiniteDimensional 𝕜 L]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] (u : L →ₗ[𝕜] M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖u x‖ ≤ C * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap u‖, norm_nonneg _, (LinearMap.toContinuousLinearMap u).le_opNorm⟩

def opEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv

lemma opn_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : opn g = ‖opEquiv n g‖ := rfl

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

lemma opn_frob_compare (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, opn g ≤ K * ‖g‖ ∧ ‖g‖ ≤ K * opn g := by
  obtain ⟨a, ha, h3⟩ := lin_bound (opEquiv n).toLinearMap
  obtain ⟨b, hb, h4⟩ := lin_bound (opEquiv n).symm.toLinearMap
  refine ⟨1 + a + b, by positivity, fun g => ?_⟩
  have h3 : ‖opEquiv n g‖ ≤ a * ‖g‖ := h3 g
  have h4 : ‖(opEquiv n).symm (opEquiv n g)‖ ≤ b * ‖opEquiv n g‖ := h4 (opEquiv n g)
  rw [LinearEquiv.symm_apply_apply] at h4
  rw [opn_eq]
  have := norm_nonneg g
  have := norm_nonneg (opEquiv n g)
  constructor <;> nlinarith

lemma opn_gN_compare (k r : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ g : Mat k r, opn g ≤ K * gN g ∧ gN g ≤ K * opn g := by
  obtain ⟨K, hK, h⟩ := opn_frob_compare (2 * r + k + 1)
  exact ⟨K, hK, fun g => by rw [gN_eq_frob]; exact h g⟩

end Frob

lemma rpow_compare {K : ℝ} (hK : 0 < K) (A : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h1 : x ≤ K * y)
    (h2 : y ≤ K * x) : x ^ A ≤ K ^ |A| * y ^ A := by
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA, ← Real.mul_rpow hK.le hy.le]
    exact Real.rpow_le_rpow hx.le h1 hA
  · have h3 : y / K ≤ x := by rw [div_le_iff₀ hK]; linarith
    have := Real.rpow_le_rpow_of_nonpos (by positivity) h3 hA
    rw [Real.div_rpow hy.le hK.le] at this
    rw [abs_of_nonpos hA, Real.rpow_neg hK.le]
    calc x ^ A ≤ y ^ A / K ^ A := this
      _ = _ := by ring

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma Dx_letter_add (b : Bool) {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y)
    (hXY : inLie k r (X + Y)) {f : Mat k r → E} (hf : CkOn 1 (GV k r) f) :
    ∀ g ∈ GV k r, Dx (b, X + Y) f g = Dx (b, X) f g + Dx (b, Y) f g := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  rw [Dx_eq, Dx_eq, Dx_eq, (Dx_hasDerivAt (x := (b, X + Y)) hXY hU hgU hg hd hff).deriv,
    (Dx_hasDerivAt (x := (b, X)) hX hU hgU hg hd hff).deriv,
    (Dx_hasDerivAt (x := (b, Y)) hY hU hgU hg hd hff).deriv, ← map_add]
  congr 1
  cases b <;> simp [dirv, Matrix.mul_add, Matrix.add_mul, add_comm]

def lieSub (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | inLie k r X}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq, inLie] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp [inLie]
  smul_mem' := fun c X hX => by
    have := lie_rsmul (X := X) hX c
    rwa [Complex.coe_smul] at this

def letterLin (p : List (Bool × Mat k r)) (hp : ∀ x ∈ p, inLie k r x.2) (b : Bool) (h : Mat k r → E)
    (hh : CkOn (p.length + 1) (GV k r) h) (g : Mat k r) (hg : g ∈ GV k r) : lieSub k r →ₗ[ℝ] E where
  toFun X := Dw p (Dx (b, X.1) h) g
  map_add' X Y := by
    rw [← Dw_add hp (CkOn_Dx (x := (b, X.1)) X.2 hh) (CkOn_Dx (x := (b, Y.1)) Y.2 hh) g hg]
    exact Dw_congr hp (Dx_letter_add b X.2 Y.2 (X + Y).2 (sCkOn_mono le_add_self hh)) g hg
  map_smul' c X := by
    have e : (c • X).1 = (c : ℂ) • X.1 := by rw [Complex.coe_smul]; rfl
    rw [e, Dx_scale, Dw_smul]
    simp

end GlobalTheory.SOrb.CCBridge

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity GlobalTheory.SOrb.CCBridge

end GlobalTheory.SOrb

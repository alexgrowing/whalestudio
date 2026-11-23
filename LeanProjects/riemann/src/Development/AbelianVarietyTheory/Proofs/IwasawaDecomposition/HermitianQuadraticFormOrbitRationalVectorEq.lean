import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

namespace GlobalTheory.GaugeEx.OrbitQuadric

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) (G : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_of_cT_mul_mul_eq {A : Type} [CommRing A] (s : A →+* A)
    (G g : Matrix (Fin M) (Fin M) A) (hg : Formalism.UG.cT s g * G * g = G) (x y : Fin M → A) :
    Formalism.UG.hform s G (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform s G x y := by
  have hc : Formalism.UG.cT s g = (g.map s)ᵀ := by
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; simp)
  rw [hc] at hg
  have hs : (fun i => s ((g *ᵥ x) i)) = (g.map s) *ᵥ (fun i => s (x i)) := by
    funext i
    exact RingHom.map_mulVec s g x i
  rw [hform_eq_dot, hform_eq_dot, hs, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose (g.map s) (fun i => s (x i)),
    ← Matrix.dotProduct_mulVec (fun i => s (x i)) (g.map s)ᵀ ((G * g) *ᵥ y),
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem hR_act (k : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J k).1 *ᵥ x) ((HA.mat R σ J k).1 *ᵥ y) = hR R σ J x y := by
  have hk : HA.mat R σ J k ∈ HR R σ J := (k : HR R σ J).2
  unfold HR Formalism.UG.UJ at hk
  have hk' : Formalism.UG.cT (sigR R σ) (HA.mat R σ J k).1 * JR R J * (HA.mat R σ J k).1 = JR R J := hk
  unfold hR
  exact hform_mulVec_mulVec_of_cT_mul_mul_eq (sigR R σ) (JR R J) _ hk' x y

theorem hR_rat (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = (1 : R) ⊗ₜ[F] hE σ J x z := by
  unfold hR hE JR
  rw [hform_eq_dot, hform_eq_dot]
  show _ = inclR R _
  rw [RingHom.map_dotProduct]
  congr 1
  all_goals funext i
  all_goals first
    | exact (RingHom.map_mulVec (inclR R) J z i).symm
    | simp [sigR, inclR]

end Form

theorem qR_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (a : F), hE σ J (x 0) (x 0) = algebraMap F E a → ∀ g : HA R σ J, qR R σ J ((g • ratTup (F := F) R x) 0) = algebraMap F R a := by
  intro F E _ _ _ _ _ σ hcm R _ _ M J x a hx g
  have hfin : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  have hact : (g • ratTup (F := F) R x) 0 = (HA.mat R σ J g).1 *ᵥ (fun i => inclR R (x 0 i)) := rfl
  rw [hact]
  unfold qR
  rw [hR_act R σ J g, hR_rat R σ J (x 0) (x 0), hx]
  have h2 : (1 : R) ⊗ₜ[F] algebraMap F E a = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]
    exact (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)).commutes a
  rw [h2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasis F E)) (algebraMap F R a),
    Fintype.card_fin, hcm.2.2.1, nsmul_eq_mul, ← mul_assoc]
  have h3 : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [h3, one_mul]

end GlobalTheory.GaugeEx.OrbitQuadric

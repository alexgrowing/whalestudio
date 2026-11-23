import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_stab_emb_baseChange {E R : Type} [Field E] [StarRing E] [CommRing R] (φ : E →+* R)
    (σ : R →+* R) (hσ : ∀ a, σ (φ a) = φ (star a)) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E) (A : Matrix (Fin n) (Fin m) E)
    (hn : m + 1 = n) (hJ : Jᴴ = J) (hd : J'.det ≠ 0) (hx : star x ⬝ᵥ (J *ᵥ x) ≠ 0)
    (hxA : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ j : Formalism.UG.UJ σ (J'.map φ) →* Formalism.UG.UJ σ (J.map φ),
      (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) ∧
        ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A.map φ =
          A.map φ * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) ∧
      ∀ h : Formalism.UG.UJ σ (J.map φ),
        ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) →
          h ∈ j.range := by
  obtain ⟨u, A', h1, h2, h3, h4, h5, h6⟩ := exists_dual_of_anisotropic_orthogonal E n m J J' x A hn hJ hd hx hxA hA
  have hsx : (fun i => σ (φ (x i))) = φ ∘ star x := by
    funext i; simp [hσ]
  have hcT : Formalism.UG.cT σ (A.map φ) = (Aᴴ).map φ := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have mv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin b → E),
      M.map φ *ᵥ (φ ∘ v) = φ ∘ (M *ᵥ v) := by
    intro a b M v; funext i; exact (RingHom.map_mulVec φ M v i).symm
  have vm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin a → E),
      (φ ∘ v) ᵥ* M.map φ = φ ∘ (v ᵥ* M) := by
    intro a b M v; funext i; exact (RingHom.map_vecMul φ M v i).symm
  have z : ∀ {a : ℕ}, φ ∘ (0 : Fin a → E) = 0 := by
    intro a; funext i; simp
  have k1 : A'.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have k2 : A'.map φ *ᵥ (φ ∘ x) = 0 := by rw [mv, h2, z]
  have k3 : (φ ∘ u) ᵥ* A.map φ = 0 := by rw [vm, h3, z]
  have k4 : (φ ∘ u) ⬝ᵥ (φ ∘ x) = 1 := by rw [← RingHom.map_dotProduct, h4, map_one]
  have k5 : vecMulVec (φ ∘ x) (φ ∘ u) + A.map φ * A'.map φ = 1 := by
    rw [← Matrix.map_one φ (map_zero φ) (map_one φ), ← h5, ← Matrix.map_mul]
    ext i j; simp [vecMulVec_apply, Matrix.mul_apply]
  obtain ⟨j, hj, hr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer R σ n m (J.map φ) (J'.map φ) (φ ∘ x) (φ ∘ u) (A.map φ) (A'.map φ)
    (by
      change IsUnit ((fun i => σ (φ (x i))) ⬝ᵥ _)
      rw [hsx, mv, ← RingHom.map_dotProduct]
      exact (IsUnit.mk0 _ hx).map φ)
    (by
      change (fun i => σ (φ (x i))) ᵥ* _ = 0
      rw [hsx, ← Matrix.map_mul, vm, hxA, z])
    (by rw [hcT, mv, mv, h6, z])
    (by rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hA])
    k1 k2 k3 k4 k5
  refine ⟨j, fun g => ⟨?_, ?_⟩, hr⟩
  · change _ *ᵥ (φ ∘ x) = φ ∘ x
    rw [hj, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, k2, Matrix.mulVec_zero, add_zero,
      Matrix.vecMulVec_mulVec, k4]
    simp
  · rw [hj, Matrix.add_mul, Matrix.mul_assoc, k1, Matrix.mul_one, Matrix.vecMulVec_mul, k3]
    ext a b; simp [vecMulVec_apply]

theorem exists_finEmb : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  intro I D s x A xf h
  obtain ⟨hn, hx, hxA, hA, -, -⟩ := h
  have hσ : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    have : I.cm.sig a = star a := rfl
    simp [Formalism.UG.sigR, Formalism.UG.inclE, this]
  have hx' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hx]; cases s <;> simp [sgn]
  exact exists_stab_emb_baseChange (Formalism.UG.inclE (F := I.F) (Af I.F)) (Formalism.UG.sigR I.cm.sig (Af I.F)) hσ
    I.J D.J x A hn I.J_herm D.J_det hx' hxA hA

end GlobalTheory.StabUnfold

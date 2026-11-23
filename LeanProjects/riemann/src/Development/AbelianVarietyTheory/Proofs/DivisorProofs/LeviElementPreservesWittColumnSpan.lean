import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem levi_mulVec_col : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) →
    ∀ {g : GAd σ J}, g ∈ levi σ J X Y S → ∀ k ∈ S,
    (matHom _ σ J g).1 *ᵥ (fun i => adMat F X i k) =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k • (fun i => adMat F X i k) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW S hS g hg k hk
  classical
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) := fun Z => rfl
  have mem : ∀ {h' : GAd σ J}, h' ∈ levi σ J X Y S → ∀ k ∈ S,
      h' ∈ frameStab σ J (initCols X k) ⊤ ∧ h' ∈ frameStab σ J (initCols Y k) ⊤ := fun hh k hk =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh k) hk)

  have fr : ∀ (C : Matrix (Fin n) (Fin r) E) (h' : GAd σ J) (k : Fin r), h' ∈ frameStab σ J (initCols C k) ⊤ →
      ∃ c : Fin r → AF F ⊗[F] E, (∀ j, k < j → c j = 0) ∧
        ∀ i, ((matHom _ σ J h').1 * adMat F C) i k = (adMat F C *ᵥ c) i := by
    rintro C h' k ⟨B, -, e⟩
    let P : Matrix (Fin r) (Fin (k.val + 1)) (AF F ⊗[F] E) :=
      (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)).submatrix id (Fin.castLE k.2)
    have hP : adMat F (initCols C k) = adMat F C * P := by
      ext i j; simp [P, initCols, Matrix.mul_apply, Matrix.one_apply]
    refine ⟨fun j => (P * B.1) j ⟨k, Nat.lt_succ_self _⟩, fun j hj => ?_, fun i => ?_⟩
    · simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, id]
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [Matrix.one_apply_ne, zero_mul]
      intro hjj
      rw [show j = _ from hjj] at hj
      exact absurd hj (not_lt.2 (Nat.le_of_lt_succ j'.2))
    · have e2 : ((matHom _ σ J h').1 * adMat F C) i k =
          ((matHom _ σ J h').1 * adMat F (initCols C k)) i ⟨k, Nat.lt_succ_self _⟩ := by
        simp [Matrix.mul_apply, initCols]
      rw [e2, e, hP, Matrix.mul_assoc]
      rfl
  set M := (matHom _ σ J g).1 with hMdef
  obtain ⟨hX, -⟩ := mem hg k hk
  obtain ⟨c, hc0, hcM⟩ := fr X g k hX
  have hYX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : ∀ j, (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k = c j := by
    intro j
    have : (fun i => (M * adMat F X) i k) = adMat F X *ᵥ c := funext hcM
    calc (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k
        = (adMat F (cT (σ : E →+* E) Y * J) *ᵥ fun i => (M * adMat F X) i k) j := by
          rw [Matrix.mul_assoc]; rfl
      _ = c j := by rw [this, mulVec_mulVec, hYX, one_mulVec]
  have hone : cT (sigR (AF F) σ) (adMat F Y) * adMat F J * adMat F X = 1 := by
    rw [c1, ← Matrix.map_mul, ← Matrix.map_mul, yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hlt : ∀ j, j < k → c j = 0 := by
    intro j hjk
    obtain ⟨-, hY⟩ := mem (inv_mem hg) j (hS k hk j hjk.le)
    obtain ⟨c', hc'0, hc'M⟩ := fr Y g⁻¹ j hY
    set Mi := (matHom _ σ J g⁻¹).1 with hMidef
    have hMMi : M * Mi = 1 := by
      rw [hMdef, hMidef, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have hu : cT (sigR (AF F) σ) M * adMat F J * M = adMat F J := g.2
    have hJM : adMat F J * M = cT (sigR (AF F) σ) Mi * adMat F J := by
      conv_rhs => rw [← hu]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
    set W : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun (m : Fin r) (_ : Fin r) => c' m with hWdef
    have hD : ∀ l, (Mi * adMat F Y) l j = (adMat F Y * W) l j := by
      intro l; rw [hc'M l]; rfl
    have e0 : adMat F (cT (σ : E →+* E) Y * J) = adMat F (cT (σ : E →+* E) Y) * adMat F J := Matrix.map_mul
    have e1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT (sigR (AF F) σ) (Mi * adMat F Y) * adMat F J := by
      rw [e0, ← c1, Matrix.mul_assoc, hJM, Formalism.UG.cT_mul, Matrix.mul_assoc]
    have key : (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k =
        (cT (sigR (AF F) σ) (adMat F Y * W) * adMat F J * adMat F X) j k := by
      rw [e1]
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hD]
    rw [← hG j, key, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (adMat F Y)), hone,
      Matrix.mul_one]
    show sigR (AF F) σ (c' k) = 0
    rw [hc'0 k hjk, map_zero]
  have hc : c = Pi.single k (c k) := by
    funext j
    rcases lt_trichotomy j k with hj | rfl | hj
    · rw [hlt j hj]; simp [Pi.single_apply, hj.ne]
    · simp
    · rw [hc0 j hj]; simp [Pi.single_apply, hj.ne']
  funext i
  calc (M *ᵥ fun i => adMat F X i k) i = (M * adMat F X) i k := rfl
    _ = (adMat F X *ᵥ c) i := hcM i
    _ = _ := by
      rw [hc, hG k]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

end GlobalTheory.IdTorus

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.AddEquivAddHaarCharEqOne

noncomputable section

namespace PI.NcVal.OmVc2

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct

theorem char_eq_one {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (e p : G ≃ₜ+ G) (hp : ∀ x, p (p x) = x) (he : ∀ x, p (e (p x)) = e.symm x) :
    addEquivAddHaarChar e = 1 := by
  have h1 : e.symm = p.trans (e.trans p) := by
    ext x
    exact (he x).symm
  have h2 : p.trans p = ContinuousAddEquiv.refl G := by
    ext x
    exact hp x
  have hpp : addEquivAddHaarChar p * addEquivAddHaarChar p = 1 := by
    rw [← addEquivAddHaarChar_trans, h2, addEquivAddHaarChar_refl]
  have h3 : (addEquivAddHaarChar e)⁻¹ = addEquivAddHaarChar e := by
    rw [← addEquivAddHaarChar_symm, h1, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans]
    calc addEquivAddHaarChar p * (addEquivAddHaarChar e * addEquivAddHaarChar p)
        = (addEquivAddHaarChar p * addEquivAddHaarChar p) * addEquivAddHaarChar e := by ring
      _ = addEquivAddHaarChar e := by rw [hpp, one_mul]
  have hpos := addEquivAddHaarChar_pos e
  have h4 : addEquivAddHaarChar e * addEquivAddHaarChar e = 1 := by
    calc addEquivAddHaarChar e * addEquivAddHaarChar e
        = addEquivAddHaarChar e * (addEquivAddHaarChar e)⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h5 : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) * (addEquivAddHaarChar e : ℝ) = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (addEquivAddHaarChar e : ℝ) := (addEquivAddHaarChar e).2
  have hx : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) = 1 := by
    rcases mul_self_eq_one_iff.1 h5 with h | h
    · exact h
    · linarith
  exact_mod_cast hx

section Alg

variable {K : Type} [CommRing K] {a M : ℕ}

def diagUnit (d : Fin a → Kˣ) : (Matrix (Fin a) (Fin a) K)ˣ where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Kˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp

theorem mulTup_diagonal (f : Fin a → K) (X : Fin a → Fin M → K) :
    mulTup (Matrix.diagonal f) X = fun j i => f j * X j i := by
  funext j i
  simp [mulTup, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq']

end Alg

section Cov

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R]

def permTup (π : Equiv.Perm (Fin n)) : (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n → Fin M → R ⊗[F] E) where
  toFun X := fun j => X (π j)
  invFun X := fun j => X (π.symm j)
  left_inv X := by funext j; simp
  right_inv X := by funext j; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem cTup_eq_one (d : Fin n → (R ⊗[F] E)ˣ) (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i)
    (hd : ∀ i, d (π i) = (d i)⁻¹) : cTup (M := M) R (diagUnit d) = 1 := by
  rw [cTup, char_eq_one (tupEquiv (M := M) (diagUnit d)) (permTup R π) ?_ ?_, inv_one]
  · intro X
    funext j
    show X (π (π j)) = X j
    rw [hπ]
  · intro X
    show (fun j => mulTup (Matrix.diagonal fun i => (d i : R ⊗[F] E)) (fun j => X (π j)) (π j)) =
      mulTup (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) X
    rw [mulTup_diagonal, mulTup_diagonal]
    funext j i
    simp [hπ, hd]

def permHerm (π : Equiv.Perm (Fin n)) : HermR R σ n ≃ₜ+ HermR R σ n where
  toFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π, fun a b => S.2 (π a) (π b)⟩
  invFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π.symm π.symm,
    fun a b => S.2 (π.symm a) (π.symm b)⟩
  left_inv S := by apply Subtype.ext; ext i j; simp
  right_inv S := by apply Subtype.ext; ext i j; simp
  map_add' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix π π).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix π.symm π.symm).subtype_mk _

theorem conjT_diagonal (f : Fin n → R ⊗[F] E) :
    conjT R σ (Matrix.diagonal f) = Matrix.diagonal fun i => sigR R σ (f i) := by
  unfold conjT
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]

theorem cHerm_eq_one [SecondCountableTopology (HermR R σ n)] (d : Fin n → (R ⊗[F] E)ˣ)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i) (hd : ∀ i, d (π i) = (d i)⁻¹) :
    cHerm σ hσ R (diagUnit d) = 1 := by
  rw [cHerm, char_eq_one (hermEquiv R σ hσ (diagUnit d)) (permHerm σ R π) ?_ ?_]
  · intro S
    apply Subtype.ext
    ext i j
    show (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (π (π i)) (π (π j)) = _
    rw [hπ, hπ]
  · intro S
    apply Subtype.ext
    ext i j
    show (conjT R σ (Matrix.diagonal fun i => (d i : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π *
          Matrix.diagonal fun i => (d i : R ⊗[F] E)) (π i) (π j) =
      (conjT R σ (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) *
          Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) i j
    rw [conjT_diagonal, conjT_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [hπ, hd]

end Cov

end PI.NcVal.OmVc2

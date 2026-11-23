import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inner_sum_left (core : InnerProductSpace.Core ℂ V) {I : Type} (s : Finset I)
    (c : I → ℂ) (u : I → V) (y : V) :
    core.inner (∑ l ∈ s, c l • u l) y = ∑ l ∈ s, (starRingEnd ℂ) (c l) * core.inner (u l) y := by
  classical
  have h0 : core.inner (0 : V) y = 0 := by
    have h := core.smul_left (0 : V) y 0
    simpa using h
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty]
    exact h0
  · rename_i a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, core.smul_left, ih]

theorem inner_sum_right (core : InnerProductSpace.Core ℂ V) {I : Type} (s : Finset I)
    (c : I → ℂ) (u : I → V) (y : V) :
    core.inner y (∑ l ∈ s, c l • u l) = ∑ l ∈ s, core.inner y (u l) * c l := by
  rw [← core.conj_inner_symm, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_left, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, Complex.conj_conj, core.conj_inner_symm, mul_comm]

theorem gram_change (core : InnerProductSpace.Core ℂ V) {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] (u : I → V) (w : J → V) (P : Matrix J I ℂ)
    (hw : ∀ j, w j = ∑ l, P j l • u l) :
    (Matrix.of fun a b => core.inner (w a) (w b)) =
      P.map (starRingEnd ℂ) * (Matrix.of fun a b => core.inner (u a) (u b)) * P.transpose := by
  ext a b
  rw [Matrix.of_apply, hw a, hw b, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_left]
  simp only [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.inner_sum_right, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem norm_det_gram (core : InnerProductSpace.Core ℂ V) {I : Type} [Fintype I]
    [DecidableEq I] (u w : I → V) (P : Matrix I I ℂ)
    (hw : ∀ j, w j = ∑ l, P j l • u l) :
    ‖(Matrix.of fun a b => core.inner (w a) (w b)).det‖ =
      ‖P.det‖ ^ 2 * ‖(Matrix.of fun a b => core.inner (u a) (u b)).det‖ := by
  have hconj : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := by
    rw [RingHom.map_det]
    rfl
  rw [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.gram_change core u w P hw, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hconj, norm_mul, norm_mul, Complex.norm_conj]
  ring

noncomputable def blockMat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => ℂ)
      (Fin.lastCases (motive := fun _ => ℂ) s d l)
      (fun j => Fin.lastCases (motive := fun _ => ℂ) 0 (C j) l) i

theorem det_blockMat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ) :
    (blockMat C d s).det = s * C.det := by
  have hsub : (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = C := by
    ext i j
    simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat, Fin.succAbove_last]
  have hsign : ((-1 : ℂ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc, hsub, hsign, _root_.one_mul]
  simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot in
theorem GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (n : ℕ)
    (β : Fin (n + 1) → V) (x : Fin n → V) (xe : V) (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ),
    (∀ j, x j = ∑ l, C j l • β l.castSucc) → xe = ∑ l, d l • β l.castSucc + s • β (Fin.last n) → s ≠ 0 →
    (Matrix.of fun a b => core.inner (x a) (x b)).det ≠ 0 → (Matrix.of fun a b => core.inner (β a) (β b)).det ≠ 0 →
    (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ - Real.log ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖) =
      Real.log ‖s‖ + (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ -
        Real.log ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖) := by
  intro V _ _ core n β x xe C d s hx hxe hs hGx hGβ
  have hy : ∀ j, (Fin.snoc x xe : Fin (n + 1) → V) j = ∑ l, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s j l • β l := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, hxe, Fin.sum_univ_castSucc]
      simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]
    · rw [Fin.snoc_castSucc, hx i, Fin.sum_univ_castSucc]
      simp [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat]
  have h1 : ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ =
      ‖(GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s).det‖ ^ 2 * ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ :=
    GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.norm_det_gram core β _ (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.blockMat C d s) hy
  have h2 : ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖ =
      ‖C.det‖ ^ 2 * ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖ :=
    GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.norm_det_gram core (fun l => β l.castSucc) x C hx
  rw [GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.GramQuot.det_blockMat] at h1
  have hx0 : ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hGx
  have hC : ‖C.det‖ ≠ 0 := by
    intro h
    apply hx0
    rw [h2, h]
    simp
  have hβ' : ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖ ≠ 0 := by
    intro h
    apply hx0
    rw [h2, h, mul_zero]
  have hβ : ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hGβ
  have hs' : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  rw [h1, h2, norm_mul, mul_pow,
    Real.log_mul (mul_ne_zero (pow_ne_zero 2 hs') (pow_ne_zero 2 hC)) hβ,
    Real.log_mul (pow_ne_zero 2 hs') (pow_ne_zero 2 hC), Real.log_mul (pow_ne_zero 2 hC) hβ',
    Real.log_pow, Real.log_pow]
  push_cast
  ring

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.RealPts

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

def mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨A, Formalism.REAL.Jm ε * Aᴴ * Formalism.REAL.Jm ε,
    by
      rw [mul_eq_one_comm]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self],
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self]⟩, h⟩

theorem uMat_mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.MainNotions.S.uMat (mkUJc ε A h) = A := rfl

theorem hpk_star (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem tauOf_spec (D : D7) (w : InfinitePlace D.host.E) : InfinitePlace.mk (embS D (tauOf D w)) = w := by
  unfold tauOf
  exact (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique (tauOf_spec D _) rfl

theorem cjw_cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    cjw D w (cjw D w M) = M := by
  unfold cjw
  split_ifs with h
  · rfl
  · funext i j
    simp

theorem cjw_injective (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N hMN
  rw [← cjw_cjw D w M, hMN, cjw_cjw]

theorem of_cjw_mul (D : D7) (w : InfinitePlace D.host.E) (A B : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    Matrix.of (cjw D w (Matrix.of.symm (Matrix.of A * Matrix.of B))) =
      Matrix.of (cjw D w A) * Matrix.of (cjw D w B) := by
  unfold cjw
  split_ifs with h
  · simp
  · ext i j
    simp [Matrix.mul_apply, star_sum]

private theorem hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have e := congrFun (congrFun (hpk_star k r) i) j
  simpa only [Matrix.map_apply] using e

theorem cjw_mem (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hM : Matrix.of M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Matrix.of (cjw D w M) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  unfold cjw
  split_ifs with h
  · exact hM
  · simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hM ⊢
    have e : (Matrix.of fun i j => star (M i j))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of fun i j => star (M i j))
        = ((Matrix.of M)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of M).map star := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum,
        star_mul', star_star, hpk_apply_of_outer_index]
    rw [e, hM, hpk_star]

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom.RealPts

theorem trX_of {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (g : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trX X C g τ) = C.Qi τ * Formalism.MainNotions.S.uMat (g (vOf X τ)) * C.Q τ := rfl

private theorem of_trX_mul_eq_mul {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s g : X.B.I.Ginf)
    (τ : D.what₂.Tau) :
    Matrix.of (trX X C (s * g) τ) = Matrix.of (trX X C s τ) * Matrix.of (trX X C g τ) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  rw [trX_of, trX_of, trX_of]
  simp only [Pi.mul_apply, Formalism.MainNotions.S.uMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

private theorem eq_of_mul_mul_eq_of_det_ne_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

private theorem hcompl_unit_property_of_isPrime {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (H N : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (hJ : Qᴴ * J * Q = H) (hN : Nᴴ * H * N = H) :
    (Q * N * Qi)ᴴ * J * (Q * N * Qi) = J := by
  have e : (Q * N * Qi)ᴴ * J * (Q * N * Qi) = Qiᴴ * (Nᴴ * (Qᴴ * J * Q) * N) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e' : (Q * Qi)ᴴ * J * (Q * Qi) = Qiᴴ * (Qᴴ * J * Q) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hJ, hN, ← hJ, ← e', hQ]
  simp

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.RealPts

theorem transport_real_points : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ),
    (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) →
      ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧
    Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧
    ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E),
      Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  intro D X θ C
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x hx
    have hM : ∀ τ, Matrix.of (cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ)))) ∈
        Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
      fun τ => cjw_mem D _ _ (hx _).1
    have hU : ∀ v, (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v)) = Formalism.REAL.Jm (X.B.I.ε v) := by
      intro v
      have hT := C.isT (X.pl v)
      simp only [IsTranspC, vOf, Equiv.symm_apply_apply] at hT
      exact hcompl_unit_property_of_isPrime _ _ _ _ _ hT.2.1 hT.2.2.1 (hM _)
    refine ⟨fun v => mkUJc (X.B.I.ε v) _ (hU v), ?_⟩
    have key : ∀ τ, trX X C (fun v => mkUJc (X.B.I.ε v) _ (hU v)) τ =
        cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ))) := by
      intro τ
      apply Matrix.of.injective
      have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
      simp only [trX_of, uMat_mkUJc, vOf, Equiv.apply_symm_apply]
      exact eq_of_mul_mul_eq_of_det_ne_zero (C.Qi τ) (C.Q τ) hQi _
    funext w
    simp only [Gm, key, tauOf_spec, cjw_cjw]
  ·
    intro s g hsg
    funext v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
    have hw := congrFun hsg (InfinitePlace.mk (embS D τ))
    simp only [Gm, tauOf_mk] at hw
    have h2 := congrArg Matrix.of (cjw_injective D _ hw)
    rw [trX_of, trX_of] at h2
    have h3 := congrArg (fun N => C.Q τ * N * C.Qi τ) h2
    simp only [eq_of_mul_mul_eq_of_det_ne_zero (C.Q τ) (C.Qi τ) (C.isT τ).2.1] at h3
    exact Subtype.ext (Units.ext h3)
  ·
    intro s g w
    simp only [Gm]
    rw [← of_cjw_mul, ← of_trX_mul_eq_mul, Equiv.symm_apply_apply]

end GlobalTheory.CovDom

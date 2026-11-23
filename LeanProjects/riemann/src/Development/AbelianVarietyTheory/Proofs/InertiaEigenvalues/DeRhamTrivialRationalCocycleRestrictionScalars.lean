import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

open Matrix

namespace GlobalTheory.PMon.DRvec

theorem blockDiag_mulVec {R : Type*} [CommRing R] {n o : Type} [Fintype n] [Fintype o] [DecidableEq o]
    (M : o → Matrix n n R) (v : n × o → R) (i : n) (m : o) :
    (Matrix.blockDiagonal M *ᵥ v) (i, m) = (M m *ᵥ fun j => v (j, m)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

theorem kd_q {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  show algebraMap (Om l) P.R.BdR (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)) = _
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem ratCocycle_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) =
      (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) →
    ∃ β : n × Fin r → P.R.BdR, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
        (fun x => P.actQdR (g : GQ l) (β x)) - β := by
  intro l _ P n _ _ K r σ ρ₀ p c c₀ hp hconj hpc hdr
  choose b hb using hdr
  let pG : GL (n × Fin r) P.R.BdR := Matrix.GeneralLinearGroup.map (kd P) p
  let β' : n × Fin r → P.R.BdR := fun x => b x.2 x.1
  have hinvmul : ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.inv_mul
  have hmulinv : (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.mul_inv
  have hpG : ∀ i j, (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j =
      kd P ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) := fun i j => rfl
  refine ⟨((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ β', fun g => ?_⟩
  set pinv := ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpinv
  set pM := (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpM
  set BD := Matrix.blockDiagonal (fun m : Fin r => matD P σ m g) with hBD
  set R0 := (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR) with hR0

  have hfix : ∀ i j, P.actQdR (g : GQ l) (pinv i j) = pinv i j := by
    let φ : P.R.BdR →+* P.R.BdR := (P.actQdR (g : GQ l)).toAlgHom.toRingHom
    have h1 : Matrix.GeneralLinearGroup.map φ pG = pG := by
      ext i j
      show φ (kd P _) = kd P _
      exact act_kd P g (hp i j)
    have h2 : Matrix.GeneralLinearGroup.map φ pG⁻¹ = pG⁻¹ := by rw [map_inv, h1]
    intro i j
    exact congrArg (fun A : GL (n × Fin r) P.R.BdR => (A : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j) h2
  have hactv : (fun x => P.actQdR (g : GQ l) ((pinv *ᵥ β') x)) = pinv *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) := by
    funext x
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hfix]

  have hd : pM * R0 = BD * pM := by
    have h1 : pM = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map (kd P) := rfl
    have h2 : R0 = ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).map (kd P) := by
      ext i j; simp [hR0, kd_q]
    have h3 : BD = (Matrix.blockDiagonal fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (kd P) := by
      rw [hBD, Matrix.blockDiagonal_map _ _ (map_zero (kd P))]
      rfl
    rw [h1, h2, h3, ← Matrix.map_mul, ← Matrix.map_mul, hconj g]
  have hR : R0 * pinv = pinv * BD := by
    calc R0 * pinv = pinv * (pM * R0) * pinv := by rw [← Matrix.mul_assoc, hinvmul, Matrix.one_mul]
    _ = pinv * (BD * pM) * pinv := by rw [hd]
    _ = pinv * BD := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hmulinv, Matrix.mul_one]
  have hvec : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = pM *ᵥ fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x) := by
    funext x
    have h := congrArg (fun v => kd P (v x)) (hpc g)
    simp only [Matrix.mulVec, dotProduct] at h ⊢
    rw [← h, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, kd_q, hpG]
  have hbt : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = BD *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) - β' := by
    funext ⟨i, m⟩
    rw [Pi.sub_apply, hBD, blockDiag_mulVec]
    exact congrFun (hb m g) i
  rw [hactv, Matrix.mulVec_mulVec, hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, ← hbt, hvec, Matrix.mulVec_mulVec,
    hinvmul, Matrix.one_mulVec]

end GlobalTheory.PMon.DRvec

end

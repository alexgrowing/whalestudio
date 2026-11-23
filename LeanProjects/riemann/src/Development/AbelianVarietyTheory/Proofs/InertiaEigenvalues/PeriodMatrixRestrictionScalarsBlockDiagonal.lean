import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem unramifiedToBst_algebraMap_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] (Bst P) q := by
  simp only [ks, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, Polynomial.algebraMap_apply]

theorem frobeniusSemistablePow_unramifiedToBst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    (phiSt P ^ m) (ks P c) = ks P (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, add_comm, fr_add, fr_one]
    have := phiSt_algebraMap P (fr l m c)
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply] at this
    exact this

theorem frobeniusSemistablePow_galoisAction_comm {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (m : ℕ) (b : Bst P) :
    (phiSt P ^ m) (actSt P g b) = actSt P g ((phiSt P ^ m) b) := by
  induction m generalizing b with
  | zero => rfl
  | succ m ih => rw [pow_succ', AlgHom.mul_apply, ih, phiSt_actSt, AlgHom.mul_apply]

end GlobalTheory.PMon

namespace GlobalTheory.PMon

theorem inv_entries_mem_finiteExtension_unramified {l : ℕ} [Fact l.Prime] {N : Type} [Fintype N] [DecidableEq N] (K : FinExt l)
    (p : GL N ↥(MaximalUnramifiedExtension l)) (h : ∀ i j, (((p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) (i j : N) :
    ((((p⁻¹ : GL N ↥(MaximalUnramifiedExtension l)) : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := by
  let S : Subfield ↥(MaximalUnramifiedExtension l) := K.1.toSubfield.comap (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
  let A : Matrix N N S := Matrix.of fun i j => ⟨(p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j, h i j⟩
  have hA : (S.subtype).mapMatrix A = (p : Matrix N N ↥(MaximalUnramifiedExtension l)) := by refine Matrix.ext fun i j => ?_; rfl
  have hmem : ((p : Matrix N N ↥(MaximalUnramifiedExtension l))⁻¹ i j) ∈ S := by
    rw [Matrix.inv_def, ← hA, ← RingHom.map_adjugate, ← RingHom.map_det]
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact S.mul_mem (S.inv_mem (A.det).2) (A.adjugate i j).2
  rw [Matrix.coe_units_inv]
  exact hmem

theorem period_resScalars : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l])
    (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) →
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    ∃ Q₀ : GL (n × Fin r) (Bst P), ∀ g : ↥(GK K),
      (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) *
        (Q₀ : Matrix (n × Fin r) (n × Fin r) (Bst P)).map (actSt P (g : GQ l)) = Q₀ := by
  intro l _ P n _ _ K r σ Q ρ₀ p h1 h2 h3
  classical
  let φm : Fin r → Bst P →+* Bst P := fun m => ((phiSt P ^ (m : ℕ) : Bst P →ₐ[ℚ_[l]] Bst P) : Bst P →+* Bst P)
  let Pu : GL (n × Fin r) (Bst P) := Units.map (RingHom.mapMatrix (m := n × Fin r) (ks P)).toMonoidHom p⁻¹
  let Du : GL (n × Fin r) (Bst P) := Units.map (Matrix.blockDiagonalRingHom n (Fin r) (Bst P)).toMonoidHom
    (MulEquiv.piUnits.symm fun m => Units.map (RingHom.mapMatrix (m := n) (φm m)).toMonoidHom Q)
  refine ⟨Pu * Du, fun g => ?_⟩
  set pv : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hpv
  have hPu : (Pu : Matrix (n × Fin r) (n × Fin r) (Bst P)) = pv.map (ks P) := rfl
  have hDu : (Du : Matrix (n × Fin r) (n × Fin r) (Bst P)) =
      Matrix.blockDiagonal fun m => (Q : Matrix n n (Bst P)).map (φm m) := rfl
  set act := actSt P (g : GQ l)

  have hPfix : (pv.map (ks P)).map act = pv.map (ks P) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact act_ks P g (inv_entries_mem_finiteExtension_unramified K p h2 i j)

  have hrel : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) * pv =
      pv * Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) := by
    have hp : pv * (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
      rw [hpv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hp' : (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * pv = 1 := by
      rw [hpv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc _ = pv * ((p : Matrix _ _ ↥(MaximalUnramifiedExtension l)) * (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map
            (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) * pv := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      _ = _ := by rw [h3, Matrix.mul_assoc, Matrix.mul_assoc, hp', Matrix.mul_one]
  have hrelB := congrArg (fun M => M.map (ks P)) hrel
  simp only [Matrix.map_mul, Matrix.map_map] at hrelB
  have hks : (ks P) ∘ (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = algebraMap ℚ_[l] (Bst P) := funext (unramifiedToBst_algebraMap_padic P)
  rw [hks, Matrix.blockDiagonal_map _ _ (map_zero _)] at hrelB

  have hblock : ∀ m : Fin r, ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) *
      ((Q : Matrix n n (Bst P)).map (φm m)).map act = (Q : Matrix n n (Bst P)).map (φm m) := by
    intro m
    have e1 : ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) =
        ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom]; exact (frobeniusSemistablePow_unramifiedToBst P m _).symm
    have e2 : ((Q : Matrix n n (Bst P)).map (φm m)).map act =
        ((Q : Matrix n n (Bst P)).map act).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom, act]; exact (frobeniusSemistablePow_galoisAction_comm P _ m _).symm
    rw [e1, e2, ← Matrix.map_mul, h1 g]
  rw [Units.val_mul, hPu, hDu, Matrix.map_mul, hPfix, Matrix.blockDiagonal_map _ _ (map_zero _),
    ← Matrix.mul_assoc, hrelB, Matrix.mul_assoc, ← Matrix.blockDiagonal_mul]
  congr 2
  funext m
  exact hblock m

end GlobalTheory.PMon

end

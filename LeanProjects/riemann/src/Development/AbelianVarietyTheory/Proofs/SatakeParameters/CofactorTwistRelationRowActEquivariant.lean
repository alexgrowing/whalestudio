import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp.Eqv

theorem degree_of_colWeight {n : ℕ} {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [colW, Pi.single_apply]

theorem rowAct_smul_matrix {n : ℕ} {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (colW n n) f ν) :
    rowAct R (c • g) f = c ^ (∑ j, ν j) • rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

theorem rowAct_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    (rowAct R (n := n) g).mapMatrix (genM R n) = (C : R →+* MP R n).mapMatrix g * genM R n := by
  ext a s : 2
  simp [rowAct, genM, Matrix.mul_apply]

theorem rowAct_det_genM {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (genM R n).det = C g.det * (genM R n).det := by
  rw [AlgHom.map_det, rowAct_genM, Matrix.det_mul, RingHom.map_det]

theorem rowAct_transpose_cofAct {n : ℕ} {R : Type} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (f : MP R n) :
    rowAct R g.transpose (cofAct R n f) = cofAct R n (rowAct R g.adjugate f) := by
  have h : (rowAct R (n := n) g.transpose).comp (cofAct R n) = (cofAct R n).comp (rowAct R g.adjugate) := by
    apply MvPolynomial.algHom_ext
    intro v
    have h1 : (rowAct R (n := n) g.transpose).mapMatrix (genM R n).adjugate =
        (genM R n).adjugate * (C : R →+* MP R n).mapMatrix g.transpose.adjugate := by
      rw [AlgHom.map_adjugate, rowAct_genM, Matrix.adjugate_mul_distrib, RingHom.map_adjugate]
    have h2 := congrFun (congrFun h1 v.2.rev) v.1
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, cofAct, aeval_X, h2, rowAct, aeval_X, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, aeval_X, aeval_C, ← Matrix.adjugate_transpose, mul_comm]
    rfl
  exact DFunLike.congr_fun h f

theorem cofRel_rowAct : ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit h.det → ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ g : MP K (m + 1), CofRel K m ν f g → CofRel K m ν (rowAct K h⁻¹ f) (h.det ^ (-(ν 0 : ℤ)) • rowAct K h.transpose g) := by
  intro K _ m ν h hh f hf g hfg
  have hd : h.det ≠ 0 := hh.ne_zero
  have hadj : h.adjugate = h.det • h⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd, one_smul]
  have hle : ν 0 ≤ ∑ i, ν i := Finset.single_le_sum (f := ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  unfold CofRel at hfg ⊢
  have h1 := congrArg (rowAct K h.transpose) hfg
  rw [rowAct_transpose_cofAct, hadj, rowAct_smul_matrix _ _ _ hf.1, map_smul, map_mul, map_pow, rowAct_det_genM,
    Matrix.det_transpose, mul_pow, ← C_pow, mul_assoc, ← smul_eq_C_mul] at h1
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [he, Nat.add_sub_cancel_left] at h1 ⊢
  rw [pow_add, mul_comm (h.det ^ ν 0), mul_smul] at h1
  have h2 : _ = _ := smul_right_injective _ (pow_ne_zero e hd) h1
  rw [mul_smul_comm, h2, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hd), one_smul]

end GlobalTheory.ValCmp.Eqv

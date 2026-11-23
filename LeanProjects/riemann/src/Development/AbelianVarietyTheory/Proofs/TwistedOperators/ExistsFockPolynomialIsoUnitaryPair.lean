import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.PolyIso

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

theorem sgn_mul_self (x : Bool) : sgn x * sgn x = 1 := by cases x <;> simp [sgn]

variable {p q r s a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b)

def fwd : LPol b a →ₐ[ℂ] Pol p q r s :=
  aeval fun v => sgn (ε v.2) • (X (e.symm v.2, e'.symm v.1) : Pol p q r s)

def bwd : Pol p q r s →ₐ[ℂ] LPol b a :=
  aeval fun l => sgn (ε (e l.1)) • (X (e' l.2, e l.1) : LPol b a)

theorem fwd_X (c : Ix r s) (x : Ix p q) :
    fwd ε e e' (X (e' c, e x)) = sgn (ε (e x)) • (X (x, c) : Pol p q r s) := by
  simp [fwd]

def kap : LPol b a ≃ₐ[ℂ] Pol p q r s :=
  AlgEquiv.ofAlgHom (fwd ε e e') (bwd ε e e')
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨x, c⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])

theorem pderiv_fwd (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    pderiv (x, c) (fwd ε e e' P) = sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [fwd]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P v hP =>
    obtain ⟨i, j⟩ := v
    obtain ⟨d, rfl⟩ := e'.surjective i
    obtain ⟨y, rfl⟩ := e.surjective j
    have h : pderiv (x, c) (fwd ε e e' (X (e' d, e y))) =
        sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) (X (e' d, e y) : LPol b a)) := by
      rw [fwd_X, Derivation.map_smul, pderiv_X, pderiv_X]
      by_cases hx : x = y
      · by_cases hc : c = d
        · subst hx hc; simp
        · simp [Ne.symm hc]
      · simp [Ne.symm hx]
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, h, hP]
    simp only [smul_eq_mul, map_add, map_mul, smul_add, mul_smul_comm]

variable {ε ε' e e'}

theorem linePos_iff (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) :
    linePos ((x, c) : Ln p q r s) = true ↔ ε' (e' c) = ε (e x) := by
  rw [h x, h' c]
  rcases x with x | x <;> rcases c with c | c <;> simp [linePos]

theorem fwd_mulX (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    fwd ε e e' (sgn (ε (e x)) • (X (e' c, e x) * P)) = X (x, c) * fwd ε e e' P := by
  rw [map_smul, map_mul, fwd_X, smul_mul_assoc, smul_smul, sgn_mul_self, one_smul]

theorem fwd_rai (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (rai ε ε' (e' c) (e x) P) = raiB (x, c) (fwd ε e e' P) := by
  unfold rai raiB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    exact fwd_mulX c x P
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    simp [pderiv_fwd]

theorem fwd_low (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (low ε ε' (e' c) (e x) P) = lowB (x, c) (fwd ε e e' P) := by
  unfold low lowB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    simp [pderiv_fwd]
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    exact fwd_mulX c x P

theorem act_eq_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Mat p q →ₗ[ℂ] V) (Z : Mat p q) :
    f Z = ∑ x, ∑ y, Z x y • f (Eab x y) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, ← map_smul, Eab, Matrix.smul_single, smul_eq_mul, mul_one]

theorem fwd_locS (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat p q) (P : LPol b a) :
    fwd ε e e' (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct1 p q r s) Z, locS, ← e.sum_comp]
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [fockAct1_Eab, ← e'.sum_comp]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [omE, LinearMap.add_apply, map_add, Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hxy : x = y <;> simp [hxy]

theorem fwd_locT (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat r s) (P : LPol b a) :
    fwd ε e e' (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct2 p q r s) Z, locT, ← e'.sum_comp]
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← e'.sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [fockAct2_Eab, ← e.sum_comp]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [omE, LinearMap.add_apply, map_add, Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hcd : c = d <;> simp [hcd]

theorem exists_isPolyIso : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a)
    (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' →
    ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ :=
  fun _ _ _ _ _ _ ε _ e e' h h' =>
    ⟨(kap ε e e').toLinearEquiv, fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩

end GlobalTheory.Chain.RealIt.PolyIso

end

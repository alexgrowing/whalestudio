import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerOfCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks

noncomputable section

open scoped TensorProduct Matrix
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.MinorCoef

section Taylor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasDerivAt_prodForm (L : ι → Module.End ℂ V) (e : ι → ℂ → V →ₗ[ℂ] ℂ)
    (h : ∀ w t f, HasDerivAt (fun s => e w s f) (e w t (L w f)) t) (t : ℂ) (T : ⨂[ℂ] _ : ι, V) :
    HasDerivAt (fun s => GlobalTheory.TensIrr.prodForm (V := fun _ : ι => V) (fun w => e w s) T)
      (GlobalTheory.TensIrr.prodForm (V := fun _ : ι => V) (fun w => e w t) (sumPl (V := fun _ : ι => V) L T)) t := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, smul_eq_mul, GlobalTheory.TensIrr.prodForm_tprod, sumPl, LinearMap.sum_apply, map_sum,
      GlobalTheory.TensIrr.atPl_tprod]
    have := (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun w _ => h w t (f w))).const_mul r
    refine this.congr_deriv ?_
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, smul_eq_mul, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

theorem isExp_taylor {L U : Module.End ℂ V} (hU : IsExp L U) (e : ℂ → V →ₗ[ℂ] ℂ)
    (h : ∀ t v, HasDerivAt (fun s => e s v) (e t (L v)) t) (v : V) : e 0 (U v) = e 1 v := by
  have hit : ∀ (n : ℕ) (v : V), iteratedDeriv n (fun s => e s v) = fun s => e s ((L ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(h s _).deriv, pow_succ', Module.End.mul_apply]
  have h1 := Complex.hasSum_taylorSeries_of_entire (f := fun s => e s v) (fun t => (h t v).differentiableAt) 0 1
  simp only [hit, sub_zero, one_pow, one_smul, smul_eq_mul, one_mul] at h1
  exact (hU v (e 0)).unique h1

end Taylor

variable {P Q R S : ℕ}

def evZ (Z : Matrix (Ix P Q) (Ix R S) ℂ) : Pol P Q R S →ₗ[ℂ] ℂ :=
  (aeval fun l : Ln P Q R S => Z l.1 l.2).toLinearMap

theorem evZ_apply (Z : Matrix (Ix P Q) (Ix R S) ℂ) (f : Pol P Q R S) :
    evZ Z f = aeval (fun l : Ln P Q R S => Z l.1 l.2) f := rfl

def OnPos (Z : Matrix (Ix P Q) (Ix R S) ℂ) : Prop := (∀ i c, Z (.inl i) (.inr c) = 0) ∧ ∀ j c, Z (.inr j) (.inl c) = 0

def shift (P Q : ℕ) : Ix R S → ℂ := Sum.elim (fun _ => ((P : ℂ) - Q) / 2) fun _ => ((Q : ℂ) - P) / 2

theorem evZ_Eab {Z : Matrix (Ix P Q) (Ix R S) ℂ} (hZ : OnPos Z) (a b : Ix R S) (hab : sameBlock a b) (f : Pol P Q R S) :
    evZ Z (fockAct2 P Q R S (Eab a b) f) =
      ∑ i, Z i a * evZ Z (pderiv (i, b) f) + (if a = b then shift P Q a else 0) * evZ Z f := by
  rw [fockAct2_Eab, LinearMap.sum_apply, map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases a with c | c <;> rcases b with d | d
  · simp only [GlobalTheory.CompactHarm.omE_pp (Sum.inl _, Sum.inl _) (Sum.inl _, Sum.inl _) rfl rfl,
      GlobalTheory.CompactHarm.omE_nn (Sum.inr _, Sum.inl _) (Sum.inr _, Sum.inl _) rfl rfl, evZ_apply, map_add, map_sub, map_neg,
      map_mul, aeval_X, hZ.2, zero_mul, neg_zero, zero_sub, Prod.mk.injEq, true_and, Sum.inl.injEq, shift, Sum.elim_inl,
      Finset.sum_add_distrib, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    split_ifs
    · simp; ring
    · simp
  · exact absurd hab (by simp [sameBlock])
  · exact absurd hab (by simp [sameBlock])
  · simp only [GlobalTheory.CompactHarm.omE_pp (Sum.inr _, Sum.inr _) (Sum.inr _, Sum.inr _) rfl rfl,
      GlobalTheory.CompactHarm.omE_nn (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, evZ_apply, map_add, map_sub, map_neg,
      map_mul, aeval_X, hZ.1, zero_mul, neg_zero, zero_sub, Prod.mk.injEq, true_and, Sum.inr.injEq, shift, Sum.elim_inr,
      Finset.sum_add_distrib, Finset.sum_const_zero, zero_add, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    split_ifs
    · simp; ring
    · simp

theorem evZ_fock {Z : Matrix (Ix P Q) (Ix R S) ℂ} (hZ : OnPos Z) {Y : Mat R S} (hY : IsKC Y) (f : Pol P Q R S) :
    evZ Z (fockAct2 P Q R S Y f) =
      ∑ l : Ln P Q R S, (Z * Y) l.1 l.2 * evZ Z (pderiv l f) + (∑ a, Y a a * shift P Q a) * evZ Z f := by
  have hYs : Y = ∑ a, ∑ b, Y a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  have term : ∀ a b : Ix R S, Y a b * evZ Z (fockAct2 P Q R S (Eab a b) f) =
      ∑ i, Z i a * Y a b * evZ Z (pderiv (i, b) f) + (if a = b then Y a a * shift P Q a * evZ Z f else 0) := by
    intro a b
    by_cases hs : sameBlock a b
    · rw [evZ_Eab hZ a b hs, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · split_ifs with e
        · subst e; ring
        · simp
    · have hab : a ≠ b := by rintro rfl; exact hs (GlobalTheory.KFixIrr.LowMinor.sameBlock_self a)
      simp [hY a b hs, hab]
  conv_lhs => rw [hYs]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, term, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Ix P Q)))]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem hasDerivAt_evZ (z : ℂ → Matrix (Ix P Q) (Ix R S) ℂ) (z' : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℂ)
    (hz : ∀ i a, HasDerivAt (fun s => z s i a) (z' i a) t) (f : Pol P Q R S) :
    HasDerivAt (fun s => evZ (z s) f) (∑ l : Ln P Q R S, z' l.1 l.2 * evZ (z t) (pderiv l f)) t := by
  induction f using MvPolynomial.induction_on with
  | C c => simpa [evZ_apply] using hasDerivAt_const t c
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p l hp =>
    have := hp.mul (hz l.1 l.2)
    simp only [evZ_apply, map_mul, aeval_X] at this ⊢
    refine this.congr_deriv ?_
    symm
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, aeval_X, mul_add, Finset.sum_add_distrib, pderiv_X,
      Finset.sum_mul]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => by ring
    · rw [Finset.sum_eq_single l]
      · simp [mul_comm]
      · intro b _ hb; simp [Pi.single_apply, hb.symm]
      · simp

theorem isKC_eq_fromBlocks {Y : Mat R S} (hY : IsKC Y) : Y = Matrix.fromBlocks Y.toBlocks₁₁ 0 0 Y.toBlocks₂₂ := by
  ext (a | a) (b | b)
  · rfl
  · exact hY _ _ (by simp [sameBlock])
  · exact hY _ _ (by simp [sameBlock])
  · rfl

theorem exp_isKC {Y : Mat R S} (hY : IsKC Y) :
    NormedSpace.exp Y = Matrix.fromBlocks (NormedSpace.exp Y.toBlocks₁₁) 0 0 (NormedSpace.exp Y.toBlocks₂₂) := by
  conv_lhs => rw [isKC_eq_fromBlocks hY]
  exact Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_fromBlocks _ _

theorem onPos_mul_exp {Z : Matrix (Ix P Q) (Ix R S) ℂ} (hZ : OnPos Z) {Y : Mat R S} (hY : IsKC Y) :
    OnPos (Z * NormedSpace.exp Y) := by
  rw [exp_isKC hY]
  constructor
  · intro i c; simp [Matrix.mul_apply, Fintype.sum_sum_type, hZ.1]
  · intro j c; simp [Matrix.mul_apply, Fintype.sum_sum_type, hZ.2]

theorem hasDerivAt_mul_exp (Z : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (t : ℂ) (i : Ix P Q) (a : Ix R S) :
    HasDerivAt (fun s : ℂ => (Z * NormedSpace.exp (s • Y)) i a) ((Z * NormedSpace.exp (t • Y) * Y) i a) t := by
  letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mat R S) := Matrix.linftyOpNormedAlgebra
  let l : Mat R S →ₗ[ℂ] ℂ :=
    { toFun := fun A => (Z * A) i a
      map_add' := fun A B => by simp [Matrix.mul_add]
      map_smul' := fun c A => by simp [Matrix.mul_smul] }
  have h := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const Y t)
  rw [Matrix.mul_assoc]
  exact h

def flow (Z : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (c t : ℂ) : Pol P Q R S →ₗ[ℂ] ℂ :=
  Complex.exp (t * (∑ a, Y a a * shift P Q a + c * Y.trace)) • evZ (Z * NormedSpace.exp (t • Y))

theorem hasDerivAt_flow {Z : Matrix (Ix P Q) (Ix R S) ℂ} (hZ : OnPos Z) {Y : Mat R S} (hY : IsKC Y) (c t : ℂ)
    (f : Pol P Q R S) : HasDerivAt (fun s => flow Z Y c s f)
      (flow Z Y c t ((fockAct2 P Q R S Y + (c * Y.trace) • (1 : Module.End ℂ (Pol P Q R S))) f)) t := by
  have hp : OnPos (Z * NormedSpace.exp (t • Y)) := onPos_mul_exp hZ fun a b h => by simp [hY a b h]
  have h1 := hasDerivAt_evZ (fun s => Z * NormedSpace.exp (s • Y)) _ t (hasDerivAt_mul_exp Z Y t) f
  have h2 := ((hasDerivAt_id t).mul_const (∑ a, Y a a * shift P Q a + c * Y.trace)).cexp
  have h3 := h2.mul h1
  simp only [flow, LinearMap.smul_apply, smul_eq_mul, LinearMap.add_apply, map_add, map_smul, Module.End.one_apply,
    evZ_fock hp hY]
  refine h3.congr_deriv ?_
  simp only [id]
  ring

variable (P Q R S) in

def base : Matrix (Ix P Q) (Ix R S) ℂ :=
  Matrix.fromBlocks (Matrix.of fun i c => if (i : ℕ) = c then 1 else 0) 0 0 (Matrix.of fun j d => if (j : ℕ) = d then 1 else 0)

theorem onPos_base : OnPos (base P Q R S) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem evZ_wit (h : P ≤ R) (k k' : ℕ) (g : Mat R Q) :
    evZ (base P Q R Q * g) (GlobalTheory.KFixIrr.LowMinor.wit P Q R Q h le_rfl k k') =
      GlobalTheory.HwCoef.leadMinor P g ^ k * (Matrix.toBlocks₂₂ g).det ^ k' := by
  rw [evZ_apply, GlobalTheory.KFixIrr.LowMinor.wit, map_mul, aeval_rename, aeval_rename, map_pow, map_pow, GlobalTheory.CharPair.detR,
    GlobalTheory.CharPair.detS, AlgHom.map_det, AlgHom.map_det]
  congr 2
  · let e : Fin P ≃ {i : Fin R // (i : ℕ) < P} :=
      ⟨fun i => ⟨Fin.castLE h i, i.2⟩, fun i => ⟨i.1, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [GlobalTheory.HwCoef.leadMinor, ← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a c
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X, Function.comp, GlobalTheory.FockSplit.jR,
      Sum.elim_inl, Matrix.mul_apply, Fintype.sum_sum_type, base, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Matrix.submatrix_apply, Matrix.toBlocks₁₁]
    rw [Finset.sum_eq_single (Fin.castLE h a)]
    · simp [e]
    · intro b _ hb
      rw [if_neg, zero_mul]
      intro e'; exact hb (Fin.ext e'.symm)
    · simp
  · congr 1
    ext a c
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X, Function.comp, GlobalTheory.FockSplit.jS,
      Sum.elim_inr, Matrix.mul_apply, Fintype.sum_sum_type, base, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.toBlocks₂₂]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg, zero_mul]
      intro e'; exact hb (Fin.ext e'.symm)
    · simp

theorem flow_wit (hS : S = Q) (h : P ≤ R) (h' : Q ≤ S) (k k' : ℕ) {Y : Mat R S} (hY : IsKC Y) (c : ℂ) (e₁ e₂ e₃ : ℤ)
    (h₁ : e₁ = k) (h₂ : (e₂ : ℂ) = ((P : ℂ) - Q) / 2 + c) (h₃ : (e₃ : ℂ) = k' + ((Q : ℂ) - P) / 2 + c) :
    flow (base P Q R S) Y c 1 (GlobalTheory.KFixIrr.LowMinor.wit P Q R S h h' k k') =
      GlobalTheory.HwCoef.coef P e₁ e₂ e₃ (NormedSpace.exp Y) := by
  subst hS
  rw [flow, LinearMap.smul_apply, one_smul, evZ_wit, GlobalTheory.HwCoef.coef, h₁, zpow_natCast, smul_eq_mul]
  have a1 : Matrix.toBlocks₁₁ (NormedSpace.exp Y) = NormedSpace.exp Y.toBlocks₁₁ := by
    rw [exp_isKC hY, Matrix.toBlocks_fromBlocks₁₁]
  have a2 : Matrix.toBlocks₂₂ (NormedSpace.exp Y) = NormedSpace.exp Y.toBlocks₂₂ := by
    rw [exp_isKC hY, Matrix.toBlocks_fromBlocks₂₂]
  rw [a1, a2, Formalism.MainNotions.DIV.Inh.det_exp, Formalism.MainNotions.DIV.Inh.det_exp, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    ← Complex.exp_nat_mul, mul_left_comm, mul_assoc, ← Complex.exp_add, ← Complex.exp_add, h₂, h₃]
  congr 2
  simp only [Matrix.trace, Fintype.sum_sum_type, shift, Sum.elim_inl, Sum.elim_inr, Matrix.diag, Matrix.toBlocks₁₁,
    Matrix.toBlocks₂₂, Matrix.of_apply, ← Finset.sum_mul]
  ring

theorem flow_zero (Z : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (c : ℂ) : flow Z Y c 0 = evZ Z := by
  simp [flow]

theorem prodForm_exp_wit {ι : Type} [Fintype ι] [DecidableEq ι] (hS : S = Q) (h : P ≤ R) (h' : Q ≤ S) (k k' : ι → ℕ)
    {Y : ι → Mat R S} (hY : ∀ w, IsKC (Y w)) (c : ι → ℂ) (e₁ e₂ e₃ : ι → ℤ) (h₁ : ∀ w, e₁ w = k w)
    (h₂ : ∀ w, (e₂ w : ℂ) = ((P : ℂ) - Q) / 2 + c w) (h₃ : ∀ w, (e₃ w : ℂ) = k' w + ((Q : ℂ) - P) / 2 + c w)
    {U : Module.End ℂ (⨂[ℂ] _ : ι, Pol P Q R S)}
    (hU : IsExp (sumPl (V := fun _ : ι => Pol P Q R S) fun w => fockAct2 P Q R S (Y w) + (c w * (Y w).trace) • 1) U) :
    GlobalTheory.TensIrr.prodForm (V := fun _ : ι => Pol P Q R S) (fun _ => evZ (base P Q R S))
      (U (PiTensorProduct.tprod ℂ fun w => GlobalTheory.KFixIrr.LowMinor.wit P Q R S h h' (k w) (k' w))) =
      ∏ w, GlobalTheory.HwCoef.coef P (e₁ w) (e₂ w) (e₃ w) (NormedSpace.exp (Y w)) := by
  have := isExp_taylor hU (fun t => GlobalTheory.TensIrr.prodForm (V := fun _ : ι => Pol P Q R S)
    fun w => flow (base P Q R S) (Y w) (c w) t)
    (hasDerivAt_prodForm _ _ fun w t f => hasDerivAt_flow onPos_base (hY w) (c w) t f)
    (PiTensorProduct.tprod ℂ fun w => GlobalTheory.KFixIrr.LowMinor.wit P Q R S h h' (k w) (k' w))
  simp only [flow_zero] at this
  rw [this, GlobalTheory.TensIrr.prodForm_tprod]
  exact Finset.prod_congr rfl fun w _ => flow_wit hS h h' _ _ (hY w) _ _ _ _ (h₁ w) (h₂ w) (h₃ w)

theorem prodForm_wit {ι : Type} [Fintype ι] [DecidableEq ι] (hS : S = Q) (h : P ≤ R) (h' : Q ≤ S) (k k' : ι → ℕ) :
    GlobalTheory.TensIrr.prodForm (V := fun _ : ι => Pol P Q R S) (fun _ => evZ (base P Q R S))
      (PiTensorProduct.tprod ℂ fun w => GlobalTheory.KFixIrr.LowMinor.wit P Q R S h h' (k w) (k' w)) = 1 := by
  subst hS
  rw [GlobalTheory.TensIrr.prodForm_tprod]
  refine Finset.prod_eq_one fun w _ => ?_
  have h1 := GlobalTheory.HwCoef.coef_one (R := R) (S := S) P (k w) 0 (k' w)
  rw [GlobalTheory.HwCoef.coef, zpow_zero, mul_one, zpow_natCast, zpow_natCast] at h1
  rw [← h1, ← evZ_wit h, Matrix.mul_one]

end GlobalTheory.MinorCoef

end

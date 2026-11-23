import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.SwapFock

open MvPolynomial

lemma sg_mul_self (e : Bool) : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e = 1 := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

lemma conj_sg (e : Bool) : starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

variable {a b : ℕ}

def swSign (ε : Fin a → Bool) (ε' : Fin b → Bool) (n : Fin b × Fin a) : ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' n.1) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε n.2)

variable (ε : Fin a → Bool) (ε' : Fin b → Bool)

lemma swSign_mul_self (n : Fin b × Fin a) : swSign ε ε' n * swSign ε ε' n = 1 := by
  unfold swSign
  rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]

lemma conj_swSign (n : Fin b × Fin a) : starRingEnd ℂ (swSign ε ε' n) = swSign ε ε' n := by
  unfold swSign
  rw [map_mul, conj_sg, conj_sg]

lemma swSign_swap (n : Fin b × Fin a) : swSign ε' ε n.swap = swSign ε ε' n := by
  unfold swSign
  exact mul_comm _ _

lemma C_swSign_mul_self {σ : Type*} (n : Fin b × Fin a) :
    (C (swSign ε ε' n) : MvPolynomial σ ℂ) * C (swSign ε ε' n) = 1 := by
  rw [← map_mul, swSign_mul_self, map_one]

lemma C_sg_mul_self {σ : Type*} (e : Bool) :
    (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) : MvPolynomial σ ℂ) * C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = 1 := by
  rw [← map_mul, sg_mul_self, map_one]

def swapHom : LPol b a →+* LPol a b :=
  eval₂Hom ((C : ℂ →+* LPol a b).comp (starRingEnd ℂ)) fun n => C (swSign ε ε' n) * X n.swap

@[simp] lemma swapHom_C (c : ℂ) : swapHom ε ε' (C c) = C (starRingEnd ℂ c) := by
  simp [swapHom]

@[simp] lemma swapHom_X (n : Fin b × Fin a) : swapHom ε ε' (X n) = C (swSign ε ε' n) * X n.swap := by
  simp [swapHom]

lemma swapHom_smul (c : ℂ) (P : LPol b a) : swapHom ε ε' (c • P) = starRingEnd ℂ c • swapHom ε ε' P := by
  rw [smul_eq_C_mul, map_mul, swapHom_C, smul_eq_C_mul]

lemma swapHom_comp : (swapHom ε' ε).comp (swapHom ε ε') = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro n
    rw [RingHom.comp_apply, swapHom_X, map_mul, swapHom_C, swapHom_X, conj_swSign, swSign_swap,
      Prod.swap_swap, ← mul_assoc, C_swSign_mul_self, one_mul, RingHom.id_apply]

lemma swapHom_pderiv (n : Fin b × Fin a) (Q : LPol b a) :
    swapHom ε ε' (pderiv n Q) = C (swSign ε ε' n) * pderiv n.swap (swapHom ε ε' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p m hp =>
    have hs := C_swSign_mul_self (σ := Fin a × Fin b) ε ε' n
    by_cases h : n = m
    · subst h
      simp only [pderiv_mul, pderiv_X_self, map_add, map_mul, hp, swapHom_X, pderiv_C, mul_one, zero_mul, zero_add]
      linear_combination (-(swapHom ε ε' p)) * hs
    · have h' : m.swap ≠ n.swap := fun e => h (Prod.swap_injective e).symm
      simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne h', map_mul, hp, swapHom_X,
        pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
      ring

lemma swapHom_rai (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (rai ε ε' i j Q) = rai ε' ε j i (swapHom ε ε' Q) := by
  unfold rai
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.neg_apply, Derivation.coeFn_coe, map_neg, swapHom_smul, swapHom_C,
      swapHom_pderiv, map_mul, conj_sg, swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (-(C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q))) * hs

lemma swapHom_low (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (low ε ε' i j Q) = low ε' ε j i (swapHom ε ε' Q) := by
  unfold low
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, Derivation.coeFn_coe, swapHom_smul, swapHom_C, swapHom_pderiv, map_mul, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q)) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs

lemma swapHom_half (c : Prop) [Decidable c] (Q : LPol b a) :
    swapHom ε ε' ((if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol b a)) else 0) Q) =
      (if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol a b)) else 0) (swapHom ε ε' Q) := by
  split_ifs
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, swapHom_smul]
    rw [map_div₀, map_one, map_ofNat]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

lemma swapHom_termT (i l : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε j l + if i = l then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

lemma swapHom_termS (i : Fin b) (j k : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε k i + if j = k then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

def swapEquiv : LPol b a ≃+ LPol a b :=
  { toFun := swapHom ε ε'
    invFun := swapHom ε' ε
    left_inv := fun P => RingHom.congr_fun (swapHom_comp ε ε') P
    right_inv := fun P => RingHom.congr_fun (swapHom_comp ε' ε) P
    map_add' := map_add _ }

lemma swapEquiv_apply (P : LPol b a) : swapEquiv ε ε' P = swapHom ε ε' P := rfl

theorem locS_locT_exchange : ∀ (a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool), ∃ j : LPol b a ≃+ LPol a b,
    (∀ (c : ℂ) P, j (c • P) = conj c • j P) ∧ ∀ P : LPol b a,
      (∀ Y : Matrix (Fin b) (Fin b) ℂ, j (locT ε ε' Y P) = locS ε' ε (Y.map (starRingEnd ℂ)) (j P)) ∧
        ∀ X : Matrix (Fin a) (Fin a) ℂ, j (locS ε ε' (X.map (starRingEnd ℂ)) P) = locT ε' ε X (j P) := by
  intro a b ε ε'
  refine ⟨swapEquiv ε ε', fun c P => ?_, fun P => ⟨fun Y => ?_, fun X => ?_⟩⟩
  · rw [swapEquiv_apply, swapEquiv_apply, swapHom_smul]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termT, Matrix.map_apply]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termS, Matrix.map_apply,
      starRingEnd_self_apply]

end GlobalTheory.Chain.RealIt.SwapFock

end

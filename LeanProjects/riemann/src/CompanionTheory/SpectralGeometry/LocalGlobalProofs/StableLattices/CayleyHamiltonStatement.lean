import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement

noncomputable section

open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk

namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm

section General

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem eval_mul_of_commute (p q : A[X]) (t : A) (h : ∀ k, Commute (q.coeff k) t) :
    (p * q).eval t = p.eval t * q.eval t :=
  eval₂_mul_noncomm (RingHom.id A) t h

theorem eval_pow_of_commute (q : A[X]) (t : A) (h : ∀ k, Commute (q.coeff k) t) (k : ℕ) :
    (q ^ k).eval t = q.eval t ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, eval_mul_of_commute _ _ _ h, ih, pow_succ]

theorem commute_alg (a : A) (y : ℂ) : Commute a (algebraMap ℂ A y) := (Algebra.commutes y a).symm

theorem eval_mul_alg (p q : A[X]) (y : ℂ) :
    (p * q).eval (algebraMap ℂ A y) = p.eval (algebraMap ℂ A y) * q.eval (algebraMap ℂ A y) :=
  eval_mul_of_commute _ _ _ fun _ => commute_alg _ y

theorem commute_coeff_X_add_C (a t : A) (h : Commute a t) (k : ℕ) :
    Commute ((X + C a : A[X]).coeff k) t := by
  rw [coeff_add, coeff_X, coeff_C]
  split_ifs <;> simp [h]

theorem eq_zero_of_eval (R : A[X]) (h : ∀ y : ℂ, R.eval (algebraMap ℂ A y) = 0) : R = 0 := by
  ext k
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  let r : ℂ[X] := ∑ i ∈ R.support, monomial i (φ (R.coeff i))
  have hr : ∀ y, r.eval y = 0 := by
    intro y
    have hy := congrArg φ (h y)
    rw [eval_eq_sum, sum_def, map_sum, map_zero] at hy
    rw [← hy]
    simp only [r, eval_finsetSum, eval_monomial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have h0 : r = 0 := Polynomial.funext (by simpa using hr)
  have hc : r.coeff k = φ (R.coeff k) := by
    simp only [r, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
    by_cases hk : R.coeff k = 0 <;> simp [hk]
  rw [← hc, h0, coeff_zero]

def PolF (f : ℂ → A) : Prop := ∃ p : A[X], ∀ y : ℂ, p.eval (algebraMap ℂ A y) = f y

theorem polF_const (a : A) : PolF fun _ : ℂ => a := ⟨C a, fun _ => eval_C⟩

theorem polF_alg (c : ℂ) : PolF fun y : ℂ => algebraMap ℂ A (y + c) :=
  ⟨X + C (algebraMap ℂ A c), fun y => by simp⟩

theorem PolF.add {f g : ℂ → A} (hf : PolF f) (hg : PolF g) : PolF fun y => f y + g y := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun y => by rw [eval_add, hp, hq]⟩

theorem PolF.mul {f g : ℂ → A} (hf : PolF f) (hg : PolF g) : PolF fun y => f y * g y := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun y => by rw [eval_mul_alg, hp, hq]⟩

theorem polF_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → A) (h : ∀ i, PolF (f i)) :
    PolF fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polF_const (0 : A)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

theorem polF_ofFn {m : ℕ} (f : Fin m → ℂ → A) (h : ∀ i, PolF (f i)) :
    PolF fun y => (List.ofFn fun i => f i y).prod := by
  induction m with
  | zero => simpa using polF_const (1 : A)
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (h 0).mul (ih _ fun i => h i.succ)

theorem polF_Tm {n : ℕ} (E : Fin n → Fin n → A) (c : ℂ) (a b : Fin n) :
    PolF fun y : ℂ => Tm E (y + c) a b := by
  unfold Tm
  by_cases hab : a = b
  · simp only [hab, if_true]
    exact (polF_alg c).add (polF_const _)
  · simp only [hab, if_false]
    exact (polF_const _).add (polF_const _)

theorem polF_qdet {n : ℕ} (E : Fin n → Fin n → A) (c : ℂ) : PolF fun y : ℂ => qdet E (y + c) := by
  unfold qdet qminor
  refine polF_sum _ _ fun σ => (polF_const _).mul ?_
  have h := polF_ofFn (fun k : Fin n => fun y : ℂ => Tm E (y + (c - (k : ℂ))) (id (σ k)) (id k))
    fun k => polF_Tm E _ _ _
  simpa only [add_sub_assoc] using h

theorem eval_map_hom {B : Type*} [Ring B] (f : A →+* B) (p : A[X]) (x : A) :
    (p.map f).eval (f x) = f (p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, eval_add, hp, hq, map_add]
  | monomial k a => simp only [map_monomial, eval_monomial, map_mul, map_pow]

theorem prod_smul_ofFn {m : ℕ} (s : ℂ) (f : Fin m → A) :
    (List.ofFn fun i => s • f i).prod = s ^ m • (List.ofFn f).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, smul_mul_smul_comm, pow_succ']

end General

variable {n : ℕ}

def liftL (V : Type) [AddCommGroup V] [Module ℂ V] (I : Type) :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (I → V) where
  toFun Z := Z.compLeft I
  map_one' := LinearMap.ext fun _ => funext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => funext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  commutes' c := LinearMap.ext fun f => funext fun i => by
    show (algebraMap ℂ (Module.End ℂ V) c) (f i) = (algebraMap ℂ (Module.End ℂ (I → V)) c f) i
    simp [Module.algebraMap_end_apply]

theorem commute_qdet_om (M : GMod n) (u : ℂ) : Commute ((qdet M.E u).compLeft (Fin n)) (om M) := by
  refine LinearMap.ext fun f => funext fun b => ?_
  have hc : ∀ (a : Fin n) (x : M.V), qdet M.E u (M.E a b x) = M.E a b (qdet M.E u x) := fun a x =>
    LinearMap.congr_fun (qDetCentral _ n M.E M.gl u a b) x
  show (qdet M.E u) (om M f b) = ∑ a, M.E a b (qdet M.E u (f a))
  rw [om_apply, map_sum]
  simp only [hc]

theorem commute_coeff_om (M : GMod n) (p : (Module.End ℂ (Fin n → M.V))[X])
    (h : ∀ y : ℂ, Commute (p.eval (algebraMap ℂ _ y)) (om M)) (k : ℕ) : Commute (p.coeff k) (om M) := by
  have h0 : p * C (om M) - C (om M) * p = 0 := eq_zero_of_eval _ fun y => by
    rw [eval_sub, eval_mul_alg, eval_mul_alg, eval_C, sub_eq_zero]
    exact h y
  have hk := congrArg (fun r => r.coeff k) h0
  simp only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero, sub_eq_zero] at hk
  exact hk

theorem root (H : QdetTens) (M : GMod n) (c : ℂ) (pC : (Module.End ℂ (Fin n → M.V))[X])
    (hC : ∀ y : ℂ, pC.eval (algebraMap ℂ _ y) = (qdet M.E (y + c)).compLeft (Fin n)) :
    pC.eval (-om M - algebraMap ℂ _ c) = 0 := by
  obtain ⟨pT, hT⟩ := polF_qdet (tensE M) c
  have hR : pT * (X + C (algebraMap ℂ _ c + om M)) - pC * (X + C (algebraMap ℂ _ (c + 1) + om M)) = 0 :=
    eq_zero_of_eval _ fun y => by
      rw [eval_sub, eval_mul_alg, eval_mul_alg, hT, hC, sub_eq_zero]
      simp only [eval_add, eval_X, eval_C]
      have h := H n M (y + c)
      have e1 : algebraMap ℂ (Module.End ℂ (Fin n → M.V)) y + (algebraMap ℂ _ c + om M) =
          (y + c) • (1 : Module.End ℂ (Fin n → M.V)) + om M := by
        rw [← add_assoc, ← map_add, Algebra.algebraMap_eq_smul_one]
      have e2 : algebraMap ℂ (Module.End ℂ (Fin n → M.V)) y + (algebraMap ℂ _ (c + 1) + om M) =
          (y + c + 1) • (1 : Module.End ℂ (Fin n → M.V)) + om M := by
        rw [← add_assoc, ← map_add, Algebra.algebraMap_eq_smul_one, add_assoc]
      rw [e1, e2]
      exact h
  have hom : Commute (om M) (-om M - algebraMap ℂ _ c) :=
    ((Commute.refl _).neg_right).sub_right (Algebra.commutes c _).symm
  have hd : ∀ d : ℂ, Commute (algebraMap ℂ (Module.End ℂ (Fin n → M.V)) d + om M) (-om M - algebraMap ℂ _ c) :=
    fun d => Commute.add_left (show Commute _ _ from Algebra.commutes d _) hom
  have ht := congrArg (eval (-om M - algebraMap ℂ _ c)) hR
  rw [eval_sub, eval_mul_of_commute _ _ _ (commute_coeff_X_add_C _ _ (hd c)),
    eval_mul_of_commute _ _ _ (commute_coeff_X_add_C _ _ (hd (c + 1)))] at ht
  simp only [eval_add, eval_X, eval_C, eval_zero] at ht
  have a1 : -om M - algebraMap ℂ _ c + (algebraMap ℂ _ c + om M) = 0 := by abel
  have a2 : -om M - algebraMap ℂ _ c + (algebraMap ℂ _ (c + 1) + om M) = 1 := by
    rw [map_add, map_one]; abel
  rw [a1, a2] at ht
  simpa using ht.symm

theorem neg_sub_algebra_map_smul_identity {A : Type*} [Ring A] [Algebra ℂ A] (w : A) (x c : ℂ) :
    -w - algebraMap ℂ A c + algebraMap ℂ A x = (-1 : ℂ) • (w - (x - c) • (1 : A)) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_smul, neg_one_smul]
  abel

theorem cayleyHam_of (H : QdetTens) : CayleyHam := by
  intro n M χ hM
  obtain ⟨k, hk⟩ := hM
  obtain ⟨pB, hB⟩ := polF_qdet M.E (cn n)
  let L := liftL M.V (Fin n)
  let pC := pB.map (L : Module.End ℂ M.V →+* Module.End ℂ (Fin n → M.V))
  have hC : ∀ y : ℂ, pC.eval (algebraMap ℂ _ y) = (qdet M.E (y + cn n)).compLeft (Fin n) := fun y => by
    have h := eval_map_hom (L : Module.End ℂ M.V →+* Module.End ℂ (Fin n → M.V)) pB (algebraMap ℂ _ y)
    have hL : (L : Module.End ℂ M.V →+* Module.End ℂ (Fin n → M.V)) (algebraMap ℂ _ y) = algebraMap ℂ _ y :=
      L.commutes y
    rw [hL, hB] at h
    exact h
  have hroot := root H M (cn n) pC hC
  let Q0 : ℂ[X] := (List.ofFn fun i => X + C (χ i)).prod
  let Q : (Module.End ℂ (Fin n → M.V))[X] := Q0.map (algebraMap ℂ _)
  have hQ : ∀ x, Q.eval x = (List.ofFn fun i => x + algebraMap ℂ _ (χ i)).prod := by
    intro x
    rw [eval_map_algebraMap, map_list_prod]
    simp [List.map_ofFn, Function.comp_def]
  have hQy : ∀ y : ℂ, Q.eval (algebraMap ℂ _ y) = Formalism.QuantumDeterminants.capP χ y • (1 : Module.End ℂ (Fin n → M.V)) := by
    intro y
    rw [hQ]
    simp only [← map_add]
    rw [← Algebra.algebraMap_eq_smul_one]
    have h := map_list_prod (algebraMap ℂ (Module.End ℂ (Fin n → M.V))) (List.ofFn fun i => y + χ i)
    rw [List.map_ofFn] at h
    simp only [Function.comp_def] at h
    rw [← h, List.prod_ofFn]
    rfl
  have hDy : ∀ y : ℂ, (pC - Q).eval (algebraMap ℂ _ y) =
      L (qdet M.E (y + cn n) - Formalism.QuantumDeterminants.capP χ y • (1 : Module.End ℂ M.V)) := by
    intro y
    rw [eval_sub, hC, hQy, map_sub, map_smul, map_one]
    rfl
  have hDk : (pC - Q) ^ k = 0 := eq_zero_of_eval _ fun y => by
    rw [eval_pow_of_commute _ _ (fun j => commute_alg _ y), hDy, ← map_pow]
    have h := hk y
    have h' : (qdet M.E (y + cn n) - Formalism.QuantumDeterminants.capP χ y • (1 : Module.End ℂ M.V)) ^ k = 0 := h
    rw [h', map_zero]
  have hCom : ∀ j, Commute ((pC - Q).coeff j) (-om M - algebraMap ℂ _ (cn n)) := by
    intro j
    have h1 : Commute (pC.coeff j) (om M) := commute_coeff_om M pC
      (fun y => by rw [hC]; exact commute_qdet_om M _) j
    have h2 : Commute (pC.coeff j) (-om M - algebraMap ℂ _ (cn n)) :=
      h1.neg_right.sub_right (commute_alg _ _)
    have h3 : ∀ z, Commute (algebraMap ℂ (Module.End ℂ (Fin n → M.V)) (Q0.coeff j)) z :=
      fun z => Algebra.commutes _ z
    rw [coeff_sub]
    refine h2.sub_left ?_
    simp only [Q, coeff_map]
    exact h3 _
  have hz := congrArg (eval (-om M - algebraMap ℂ _ (cn n))) hDk
  rw [eval_pow_of_commute _ _ hCom, eval_zero, eval_sub, hroot, hQ, zero_sub] at hz
  have hf : (fun i => -om M - algebraMap ℂ _ (cn n) + algebraMap ℂ _ (χ i)) =
      fun i => (-1 : ℂ) • (om M - (χ i - cn n) • (1 : Module.End ℂ (Fin n → M.V))) := by
    funext i
    rw [neg_sub_algebra_map_smul_identity]
  rw [hf, prod_smul_ofFn, ← neg_smul, _root_.smul_pow] at hz
  exact ⟨k, (smul_eq_zero.1 hz).resolve_left
    (pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero _ (by norm_num))))⟩

theorem cayleyHam : CayleyHam := cayleyHam_of GlobalTheory.T.QuantumDeterminantTensor

end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm

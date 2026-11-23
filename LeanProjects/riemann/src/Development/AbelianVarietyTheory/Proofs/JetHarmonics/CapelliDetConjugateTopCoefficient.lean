import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.CapelliTop

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem prod_ofFn_sum_smul {t n : ℕ} (q : Fin t → Fin n → ℂ) (x : Fin t → Fin n → A) :
    (List.ofFn fun k : Fin t => ∑ d, q k d • x k d).prod =
      ∑ d : Fin t → Fin n, (∏ k, q k (d k)) • (List.ofFn fun k => x k (d k)).prod := by
  classical
  rw [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply]

theorem qminor_eq_zero {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (d : Fin n → Fin n)
    (hd : ¬ Function.Injective d) (u : ℂ) : qminor E id d u = 0 := by
  simp only [Function.Injective, not_forall] at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have h := quantumMinorColSkew_holds A n n E hE id d (Equiv.swap i j) u
  have e : d ∘ Equiv.swap i j = d := by
    funext k
    exact Equiv.apply_swap_eq_self hij k
  rw [e, Equiv.Perm.sign_swap hne] at h
  apply eq_zero_of_add_self_eq_zero
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  exact add_eq_zero_iff_eq_neg.mpr h

theorem det_smul_qdet {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u : ℂ) : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod := by
  classical
  have h1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • qminor E id d u := by
    simp only [Finset.smul_sum, qminor]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [prod_ofFn_sum_smul (fun k d => Q k d) (fun k d => Tm E (u - (k : ℂ)) (σ k) d),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  rw [h1, ← Matrix.det_transpose, Matrix.det_apply', Finset.sum_smul]
  refine Fintype.sum_of_injective (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n))
    DFunLike.coe_injective _ _ ?_ ?_
  · intro d hd
    rw [qminor_eq_zero E hE d, smul_zero]
    intro hinj
    exact hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.mp hinj), rfl⟩
  · intro τ
    have h := quantumMinorColSkew_holds A n n E hE id id τ u
    rw [Function.id_comp] at h
    rw [h, mul_comm, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl

theorem mul_pow_shift (x y δ : A) (h : x * δ = δ * (x + y)) (hy : y * δ = δ * y) (s : ℕ) :
    x * δ ^ s = δ ^ s * (x + (s : ℂ) • y) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, add_mul, h, smul_mul_assoc, hy,
      Nat.cast_succ, add_smul, one_smul, ← mul_smul_comm, ← mul_add]
    congr 2
    abel

theorem prod_ofFn_semiconj {t : ℕ} (x y : Fin t → A) (g : A) (h : ∀ k, x k * g = g * y k) :
    (List.ofFn x).prod * g = g * (List.ofFn y).prod := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [mul_assoc, ih _ _ (fun k => h k.succ), ← mul_assoc, h, mul_assoc]

theorem pt_prod {t : ℕ} (x y : Fin t → A) :
    TL.PT t (fun s : ℂ => (List.ofFn fun k => x k + s • y k).prod) (List.ofFn y).prod := by
  induction t with
  | zero => exact (TL.PT.const 1).congr (fun s => by simp) (by simp)
  | succ t ih =>
    have h := ih (fun k => x k.succ) (fun k => y k.succ)
    refine ((h.mulL (x 0)).up.add (h.mulL (y 0)).mulS).congr (fun s => ?_) ?_
    · simp only [List.ofFn_succ, List.prod_cons, add_mul, smul_mul_assoc]
    · simp only [List.ofFn_succ, List.prod_cons, zero_add]

theorem sum_smul_Tm {n : ℕ} (E : Fin n → Fin n → A) (q : Fin n → ℂ) (u : ℂ) (a : Fin n) :
    ∑ d, q d • Tm E u a d = (q a * u) • (1 : A) + ∑ d, q d • E a d := by
  simp [shiftedGenerator_eq_ite_smul_add, Finset.sum_add_distrib, smul_smul, ite_smul]

theorem top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  intro A _ _ p m E Q δ ν u hE h1 h2 h3
  set X : Equiv.Perm (Fin (p + m)) → Fin p → A := fun σ k =>
    ∑ d, Q (Fin.castAdd m k) d • Tm E (u - ((k : ℕ) : ℂ)) (σ (Fin.castAdd m k)) d with hX
  set Y : Equiv.Perm (Fin (p + m)) → A := fun σ => (List.ofFn fun k : Fin m =>
    ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod with hY
  have e1 : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn (X σ)).prod * Y σ) := by
    rw [det_smul_qdet E hE]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [List.ofFn_add, List.prod_append]
    simp only [hX, hY, Fin.val_natAdd, Nat.cast_add, sub_sub]
    rfl
  have eY : ∀ σ (s : ℕ), Y σ * δ ^ s = δ ^ s * Y σ := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => Commute.pow_right (?_ : _ * _ = _ * _) s
    rw [sum_smul_Tm, add_mul, mul_add, h2]
    simp
  have eX : ∀ σ (s : ℕ), (List.ofFn (X σ)).prod * δ ^ s =
      δ ^ s * (List.ofFn fun k => X σ k + (s : ℂ) • ν (σ (Fin.castAdd m k)) k).prod := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => mul_pow_shift _ _ _ ?_ (h3 _ _) s
    simp only [hX]
    rw [sum_smul_Tm, add_mul, h1, add_assoc, mul_add δ (_ • _)]
    simp
  have e2 : ∀ s : Fin (p + 1), Q.det • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) =
      ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (δ ^ p *
        ((List.ofFn fun k => X σ k + ((s : ℕ) : ℂ) • ν (σ (Fin.castAdd m k)) k).prod * Y σ)) := by
    intro s
    rw [← mul_smul_comm, ← smul_mul_assoc, e1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc, eY, ← mul_assoc _ (δ ^ (s : ℕ)), eX, mul_assoc,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp s.isLt)]
  rw [Finset.smul_sum, Finset.mul_sum]
  simp only [smul_comm Q.det, e2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := (((pt_prod (X σ) (fun k => ν (σ (Fin.castAdd m k)) k)).mulR (Y σ)).mulL (δ ^ p)).lag
  rw [mul_smul_comm]
  refine Eq.trans ?_ (congrArg _ h.symm)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

end GlobalTheory.CapelliTop

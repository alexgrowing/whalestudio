import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.TLie

variable {R S : ℕ}

lemma adCoeff_eq (Z : Mat R S) (y x : NC R S) :
    adP Z y x = (Z * eNC x - eNC x * Z) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  obtain ⟨⟨c, d⟩, h'⟩ := x
  simp only [adP, eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [Finset.sum_eq_single c]
    · by_cases hbd : b = d
      · simp [hbd]
      · simp [hbd, Ne.symm hbd]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · rw [Finset.sum_eq_single d]
    · by_cases hac : a = c
      · simp [hac]
      · simp [hac, Ne.symm hac]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

lemma same_trans {a b c : Ix R S} (h1 : sameBlock a b) (h2 : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> first | trivial | exact h1.elim | exact h2.elim

lemma sum_NC (f : Ix R S × Ix R S → ℂ) (hf : ∀ p, sameBlock p.1 p.2 → f p = 0) :
    ∑ x : NC R S, f x.1 = ∑ p, f p := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Ix R S × Ix R S => ¬ sameBlock p.1 p.2)
    (fun p => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)) f]
  exact Finset.sum_filter_of_ne fun p _ hp hs => hp (hf p hs)

lemma sum_all {ι : Type} [Fintype ι] [DecidableEq ι] (Y M : Matrix ι ι ℂ) (a b : ι) :
    ∑ p : ι × ι, (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2 =
      (Y * M - M * Y) a b := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.mul_apply]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    simp [mul_comm]

lemma sum_adP {Y : Mat R S} (hY : IsKC Y) (M : Mat R S) (y : NC R S) :
    ∑ x : NC R S, adP Y y x * M x.1.1 x.1.2 = (Y * M - M * Y) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  refine Eq.trans ?_ (sum_all Y M a b)
  refine sum_NC (fun p =>
    (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2) ?_
  rintro ⟨c, d⟩ hs
  have e1 : Y a c * (if b = d then 1 else 0) = 0 := by
    split_ifs with hbd
    · subst hbd
      rw [hY a c (fun hac => h (same_trans hac hs)), zero_mul]
    · exact mul_zero _
  have e2 : (if a = c then 1 else 0) * Y d b = 0 := by
    split_ifs with hac
    · subst hac
      rw [hY d b (fun hdb => h (same_trans hs hdb)), mul_zero]
    · exact zero_mul _
  simp only [e1, e2, sub_zero, zero_mul]

lemma adCoeff_commutator {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) (y w : NC R S) :
    adP (Y * Z - Z * Y) y w = ∑ x, adP Y y x * adP Z x w - ∑ x, adP Z y x * adP Y x w := by
  have h1 := sum_adP hY (Z * eNC w - eNC w * Z) y
  have h2 := sum_adP hZ (Y * eNC w - eNC w * Y) y
  simp only [← adCoeff_eq] at h1 h2
  rw [h1, h2, adCoeff_eq, ← Matrix.sub_apply]
  refine congrFun (congrFun ?_ _) _
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

variable {W : Type} [AddCommGroup W] [Module ℂ W]

lemma factorOp_apply (k : ℕ) (i : Fin k) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    factorOp k i Z Ψ g = ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := rfl

lemma factorOp_commutator (k : ℕ) (i : Fin k) {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) :
    (factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k i Y * factorOp k i Z - factorOp k i Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, factorOp_apply,
    Function.update_self, Function.update_idem, adCoeff_commutator hY hZ, sub_smul, Finset.sum_sub_distrib,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  congr 1 <;> exact Finset.sum_comm

lemma factorOp_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (Y Z : Mat R S) :
    (factorOp k i Y * factorOp k j Z : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k j Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [Module.End.mul_apply, factorOp_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm, Function.update_comm hij]

def ptOp (k : ℕ) (A : Module.End ℂ W) : Module.End ℂ ((Fin k → NC R S) → W) :=
  LinearMap.pi (fun g => A ∘ₗ LinearMap.proj g)

lemma ptOp_comm_factorOp (k : ℕ) (i : Fin k) (A : Module.End ℂ W) (Z : Mat R S) :
    (ptOp k A * factorOp k i Z : Module.End ℂ ((Fin k → NC R S) → W)) = factorOp k i Z * ptOp k A := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp [ptOp, factorOp_apply]

lemma tAct_eq (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) :
    tAct k actW Z = ptOp k (actW Z) + ∑ i, factorOp k i Z := rfl

theorem isKLieAct_tAct (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (h : IsKLieAct actW) : IsKLieAct (tAct k actW) := by
  intro Y Z hY hZ
  have hp : (ptOp k (actW (Y * Z - Z * Y)) : Module.End ℂ ((Fin k → NC R S) → W)) =
      ptOp k (actW Y) * ptOp k (actW Z) - ptOp k (actW Z) * ptOp k (actW Y) := by
    rw [h Y Z hY hZ]
    refine LinearMap.ext fun Ψ => funext fun g => ?_
    simp [ptOp]
  have hs : (∑ i, factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      (∑ i, factorOp k i Y) * (∑ i, factorOp k i Z) - (∑ i, factorOp k i Z) * (∑ i, factorOp k i Y) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun i j => (factorOp k i Z * factorOp k j Y :
        Module.End ℂ ((Fin k → NC R S) → W))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i, factorOp_commutator k i hY hZ]
    · intro j _ hj
      rw [factorOp_comm_of_ne k hj.symm, sub_self]
    · simp
  have hc : ∀ (A : Module.End ℂ W) (X : Mat R S),
      (ptOp k A * (∑ i, factorOp k i X) : Module.End ℂ ((Fin k → NC R S) → W)) =
        (∑ i, factorOp k i X) * ptOp k A := by
    intro A X
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => ptOp_comm_factorOp k i A X
  rw [tAct_eq, tAct_eq, tAct_eq, hp, hs]
  simp only [add_mul, mul_add, hc]
  abel

end GlobalTheory.SteepMult.TLie

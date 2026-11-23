import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentralStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

def hwRowSum (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) : R :=
  ∑ l, (hcMat R μ ^ k) i l

theorem hwRowSum_zero (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) :
    hwRowSum R μ 0 i = 1 := by
  simp [hwRowSum, Matrix.one_apply]

theorem hwRowSum_succ_eq_mul (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i = ∑ m, hcMat R μ i m * hwRowSum R μ k m := by
  simp only [hwRowSum, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem hwRowSum_succ (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i =
      ∑ l, (if l < i then 0 else if l = i then μ i * hwRowSum R μ k i
        else hwRowSum R μ k i - hwRowSum R μ k l) := by
  rw [hwRowSum_succ_eq_mul]
  set r := hwRowSum R μ k with hr
  have h1 : ∀ l, hcMat R μ i l * r l =
      (if l = i then μ i * r i else 0) + (if l = i then ((N - 1 - i.val : ℕ) : R) * r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp [hcMat, shift, add_mul]
    · by_cases hil : i < l
      · simp [hcMat, hl, hil]
      · simp [hcMat, hl, hil]
  have h2 : ∀ l, (if l < i then 0 else if l = i then μ i * r i else r i - r l) =
      (if l = i then μ i * r i else 0) + (if i < l then r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h
      simp
    · simp [h, h.ne', h.not_gt]
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  have h3 : ∑ l : Fin N, (if i < l then r i else 0) = ((N - 1 - i.val : ℕ) : R) * r i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i := by
      ext l
      simp
    rw [this, Fin.card_Ioi]
  rw [h3]
  simp

theorem pow_entry_stable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (k : ℕ) :
    ∀ a b, ∀ f ∈ M, (E ^ k) a b f ∈ M := by
  induction k with
  | zero =>
    intro a b f hf
    by_cases h : a = b
    · subst h
      simpa [Matrix.one_apply] using hf
    · simp [Matrix.one_apply, h]
  | succ k ih =>
    intro a b f hf
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun l _ => hM a l _ (ih l b f hf)

theorem hw_pow_entries {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (hE : GlRel E) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (μ : Fin N → R) (v : V)
    (hup : ∀ a b, a < b → E a b v ∈ M) (hd : ∀ a, E a a v - μ a • v ∈ M) (k : ℕ) :
    (∀ i j, i < j → (E ^ k) i j v ∈ M) ∧ (∀ i, (E ^ k) i i v - hwRowSum R μ k i • v ∈ M) := by
  induction k with
  | zero =>
    constructor
    · intro i j hij
      simp [Matrix.one_apply, hij.ne]
    · intro i
      simp [hwRowSum_zero, Matrix.one_apply]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcomm := (GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central (Module.End R V) N E hE k).1
    have hst := pow_entry_stable E M hM k
    have key : ∀ i j l, i < l →
        E i l ((E ^ k) l j v) - ((E ^ k) i j v - (if j = i then (E ^ k) l l v else 0)) ∈ M := by
      intro i j l hil
      have h := LinearMap.congr_fun (hcomm i l l j) v
      have h' : E i l ((E ^ k) l j v) - (E ^ k) l j (E i l v) =
          (E ^ k) i j v - (if j = i then (E ^ k) l l v else 0) := by
        by_cases hji : j = i
        · simpa [hji, Module.End.mul_apply] using h
        · simpa [hji, Module.End.mul_apply] using h
      have h2 : (E ^ k) l j (E i l v) ∈ M := hst l j _ (hup i l hil)
      rw [← h']
      simpa using h2
    constructor
    · intro i j hij
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l j with h | h | h
      · exact hM i l _ (ih1 l j h)
      · subst h
        have h1 := hM i l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hup i l hij)
        simpa using M.add_mem h1 h2
      · have h1 := key i j l (hij.trans h)
        rw [if_neg hij.ne'] at h1
        simpa using M.add_mem h1 (ih1 i j hij)
    · intro i
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply, hwRowSum_succ, Finset.sum_smul,
        ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l i with h | h | h
      · simpa [h] using hM i l _ (ih1 l i h)
      · subst h
        have h1 := hM l l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hd l)
        have h3 := M.add_mem h1 h2
        have e : E l l ((E ^ k) l l v) - hwRowSum R μ k l • E l l v +
            hwRowSum R μ k l • (E l l v - μ l • v) =
            E l l ((E ^ k) l l v) - (μ l * hwRowSum R μ k l) • v := by
          rw [smul_sub, smul_smul, mul_comm (hwRowSum R μ k l)]
          abel
        rw [e] at h3
        simpa using h3
      · have h1 := key i i l h
        rw [if_pos rfl] at h1
        have h3 := M.sub_mem (M.add_mem h1 (ih2 i)) (ih2 l)
        have e : E i l ((E ^ k) l i v) - ((E ^ k) i i v - (E ^ k) l l v) +
            ((E ^ k) i i v - hwRowSum R μ k i • v) - ((E ^ k) l l v - hwRowSum R μ k l • v) =
            E i l ((E ^ k) l i v) - (hwRowSum R μ k i - hwRowSum R μ k l) • v := by
          rw [sub_smul]
          abel
        rw [e] at h3
        simpa [h.not_gt, h.ne'] using h3

theorem trace_pow_hw : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ)
    (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V),
    (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) →
    (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  intro R V _ _ _ N E hE M hM μ v hup hd k
  have h := (hw_pow_entries E hE M hM μ v hup hd k).2
  have e : (E ^ k).trace v - hcVal R μ k • v = ∑ i, ((E ^ k) i i v - hwRowSum R μ k i • v) := by
    simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, hcVal, Finset.sum_sub_distrib,
      Finset.sum_smul, hwRowSum]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => h i

end GlobalTheory.Alc

import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.NonRelPf

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

@[reducible] def qMod (S : HSpace E) : Module ℚ (Module.End E S.V) :=
  Module.compHom (Module.End E S.V) (algebraMap ℚ E)

attribute [local instance] qMod

theorem qsmul_apply (q : ℚ) (A : Module.End E S.V) (x : S.V) : (q • A) x = (algebraMap ℚ E q) • A x := rfl

section Xa

variable (F : FlagG S r T)

theorem Xa_zero : F.Xa 0 = ⊥ := by
  unfold FlagG.Xa
  simp

theorem Xa_mono {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := Submodule.span_mono (Set.image_mono fun (i : Fin r) (hi : i.1 < a) => lt_of_lt_of_le hi h)

theorem Xa_ge {a : ℕ} (h : r ≤ a) : F.Xa a = F.X := by
  unfold FlagG.Xa FlagG.X
  have hu : {i : Fin r | i.1 < a} = Set.univ := Set.eq_univ_of_forall fun i => lt_of_lt_of_le i.2 h
  rw [hu, Set.image_univ]

theorem Xa_min (a : ℕ) : F.Xa a = F.Xa (min a r) := by
  rcases le_total a r with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Xa_ge F h, Xa_ge F le_rfl]

theorem e_mem_Xa (a : Fin r) : F.e a ∈ F.Xa (a.1 + 1) := Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem hT_Xa_zero (f : S.V) (a : ℕ) (hf : ∀ b : Fin r, b.1 < a → S.hT f (F.e b) = 0) {x : S.V}
    (hx : x ∈ F.Xa a) : S.hT f x = 0 := by
  have hle : F.Xa a ≤ LinearMap.ker (S.hT f) := by
    unfold FlagG.Xa
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact LinearMap.mem_ker.mpr (hf b hb)
  exact LinearMap.mem_ker.mp (hle hx)

theorem hT_eq_coefX (f : S.V) (a : Fin r) (hf : ∀ b, S.hT f (F.e b) = if b = a then 1 else 0) {x : S.V}
    (hx : x ∈ F.X) : S.hT f x = F.coefX x a := by
  classical
  have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
  have hc : F.coefX x a = F.e_indep.repr ⟨x, hx'⟩ a := by
    simp [FlagG.coefX, hx']
  rw [hc]
  have hsum : x = ∑ b, F.e_indep.repr ⟨x, hx'⟩ b • F.e b := by
    have h1 := F.e_indep.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    exact h1.symm
  conv_lhs => rw [hsum]
  simp [map_sum, map_smul, hf]

end Xa

section Lie

variable {F : FlagG S r T} {Y : Module.End E S.V}

theorem lie_skew_pow (hY : Y ∈ F.LieN) (k : ℕ) (x y : S.V) :
    S.hT x ((Y ^ k) y) = (-1) ^ k * S.hT ((Y ^ k) x) y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    have h1 : (Y ^ (k + 1)) y = (Y ^ k) (Y y) := by rw [pow_succ, Module.End.mul_apply]
    have h2 : (Y ^ (k + 1)) x = Y ((Y ^ k) x) := by rw [pow_succ', Module.End.mul_apply]
    have h3 := hY.1 ((Y ^ k) x) y
    rw [h1, h2, ih, pow_succ]
    linear_combination ((-1 : E) ^ k) * h3

theorem lie_Xa (hY : Y ∈ F.LieN) {j : ℕ} (hj : j ≤ r) {x : S.V} (hx : x ∈ F.Xa j) : Y x ∈ F.Xa (j - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [Xa_zero F] at hx
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  · exact hY.2.1 j hj0 hj x hx

theorem lie_pow_Xa (hY : Y ∈ F.LieN) (k : ℕ) {j : ℕ} (hj : j ≤ r) {x : S.V} (hx : x ∈ F.Xa j) :
    (Y ^ k) x ∈ F.Xa (j - k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← Nat.sub_sub]
    exact lie_Xa hY (le_trans (Nat.sub_le j k) hj) ih

theorem lie_X (hY : Y ∈ F.LieN) {x : S.V} (hx : x ∈ F.X) : Y x ∈ F.X := by
  rw [← Xa_ge F (le_refl r)] at hx ⊢
  exact Xa_mono F (Nat.sub_le r 1) (lie_Xa hY le_rfl hx)

theorem lie_pow_X (hY : Y ∈ F.LieN) (k : ℕ) {x : S.V} (hx : x ∈ F.X) : (Y ^ k) x ∈ F.X := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact lie_X hY ih

theorem lie_pow_r_X (hY : Y ∈ F.LieN) {x : S.V} (hx : x ∈ F.X) : (Y ^ r) x = 0 := by
  rw [← Xa_ge F (le_refl r)] at hx
  have h := lie_pow_Xa hY r le_rfl hx
  rw [Nat.sub_self, Xa_zero F] at h
  exact (Submodule.mem_bot E).1 h

theorem lie_pow_r_perp (hY : Y ∈ F.LieN) (y : S.V) : (Y ^ r) y ∈ perpS S F.X := by
  show ∀ x ∈ F.X, S.hT x ((Y ^ r) y) = 0
  intro x hx
  rw [lie_skew_pow hY, lie_pow_r_X hY hx, map_zero, LinearMap.zero_apply, mul_zero]

theorem lie_nilp (hY : Y ∈ F.LieN) : Y ^ (2 * r + 1) = 0 := by
  have hp : Y ^ (2 * r + 1) = Y ^ r * Y * Y ^ r := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  apply LinearMap.ext
  intro v
  have h3 := lie_pow_r_X hY (hY.2.2 _ (lie_pow_r_perp hY v))
  rw [hp, Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply]
  exact h3

end Lie

section Exp

variable {F : FlagG S r T} {Y : Module.End E S.V} (s : E)

def nexp (Y : Module.End E S.V) (s : E) : Module.End E S.V := IsNilpotent.exp (s • Y)

theorem sY_nilp (hY : Y ∈ F.LieN) : (s • Y) ^ (2 * r + 1) = 0 := by
  rw [smul_pow, lie_nilp hY, smul_zero]

theorem sY_isNilp (hY : Y ∈ F.LieN) : IsNilpotent (s • Y) := ⟨2 * r + 1, sY_nilp s hY⟩

theorem nexp_apply (hY : Y ∈ F.LieN) (x : S.V) :
    nexp Y s x = ∑ i ∈ Finset.range (2 * r + 1), (algebraMap ℚ E (i.factorial : ℚ)⁻¹ * s ^ i) • (Y ^ i) x := by
  unfold nexp
  rw [IsNilpotent.exp_eq_sum (sY_nilp s hY), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qsmul_apply, smul_pow, LinearMap.smul_apply, mul_smul]

variable {s}

theorem star_alg_rat (q : ℚ) : star (algebraMap ℚ E q) = algebraMap ℚ E q := by
  rw [eq_ratCast (algebraMap ℚ E) q]
  exact star_ratCast q

theorem nexp_adj (hY : Y ∈ F.LieN) (hs : star s = s) (x y : S.V) :
    S.hT (nexp Y s x) y = S.hT x (nexp Y (-s) y) := by
  rw [nexp_apply s hY, nexp_apply (-s) hY, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsk := lie_skew_pow hY i x y
  have hsk' : S.hT ((Y ^ i) x) y = (-1) ^ i * S.hT x ((Y ^ i) y) := by
    rw [hsk, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply,
    star_mul', star_pow, hs, star_alg_rat]
  rw [hsk', neg_pow s i]
  ring

theorem nexp_mul_neg (hY : Y ∈ F.LieN) : nexp Y s * nexp Y (-s) = 1 := by
  letI : Algebra ℚ (Module.End E S.V) := Algebra.compHom (Module.End E S.V) (algebraMap ℚ E)
  have hc : Commute (s • Y) ((-s) • Y) := ((Commute.refl Y).smul_left s).smul_right (-s)
  have key := IsNilpotent.exp_add_of_commute hc (sY_isNilp s hY) (sY_isNilp (-s) hY)
  have h0 : s • Y + (-s) • Y = 0 := by rw [neg_smul, add_neg_cancel]
  rw [h0, IsNilpotent.exp_zero] at key
  exact key.symm

theorem nexp_neg_mul (hY : Y ∈ F.LieN) : nexp Y (-s) * nexp Y s = 1 := by
  have h := nexp_mul_neg (s := -s) hY
  rwa [neg_neg] at h

def nexpE (hY : Y ∈ F.LieN) (s : E) : S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (nexp Y s) (nexp Y (-s)) (nexp_mul_neg hY) (nexp_neg_mul hY)

theorem nexpE_apply (hY : Y ∈ F.LieN) (x : S.V) : nexpE hY s x = nexp Y s x := rfl

theorem nexpE_isom (hY : Y ∈ F.LieN) (hs : star s = s) : nexpE hY s ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  show ∀ x y, S.hT (nexpE hY s x) (nexpE hY s y) = S.hT x y
  intro x y
  rw [nexpE_apply, nexpE_apply, nexp_adj hY hs, ← Module.End.mul_apply, nexp_neg_mul hY,
    Module.End.one_apply]

theorem nexp_sub (hY : Y ∈ F.LieN) (x : S.V) :
    nexp Y s x - x = ∑ i ∈ Finset.Ico 1 (2 * r + 1), (algebraMap ℚ E (i.factorial : ℚ)⁻¹ * s ^ i) • (Y ^ i) x := by
  rw [nexp_apply s hY, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp

theorem nexp_Xa (hY : Y ∈ F.LieN) (j : ℕ) {x : S.V} (hx : x ∈ F.Xa (j + 1)) : nexp Y s x - x ∈ F.Xa j := by
  rw [nexp_sub hY]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
  rw [Xa_min F (j + 1)] at hx
  exact Xa_mono F (by omega) (lie_pow_Xa hY i (min_le_right _ _) hx)

theorem nexp_perp (hY : Y ∈ F.LieN) {x : S.V} (hx : x ∈ perpS S F.X) : nexp Y s x - x ∈ F.X := by
  rw [nexp_sub hY]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := (Finset.mem_Ico.1 hi).1; omega⟩
  rw [pow_succ, Module.End.mul_apply]
  exact lie_pow_X hY k (hY.2.2 x hx)

theorem nexp_root (hY : Y ∈ F.LieN) (f : S.V) (a : Fin r)
    (hf : ∀ b, S.hT f (F.e b) = if b = a then 1 else 0) (hfz : S.hT f F.z = 0) :
    S.hT f (nexp Y s (F.fvec a.succ)) = s * F.coefX (Y (F.fvec a.succ)) a := by
  have ha := a.isLt
  have hXa1 : F.Xa (a.1 + 1) ≤ F.X := by
    rw [← Xa_ge F (le_refl r)]
    exact Xa_mono F ha
  have hzperp : F.z ∈ perpS S F.X := by
    show ∀ x ∈ F.X, S.hT x F.z = 0
    intro x hx
    change x ∈ Submodule.span E (Set.range F.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact F.z_orth b
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  obtain ⟨hw, hfv⟩ : Y (F.fvec a.succ) ∈ F.Xa (a.1 + 1) ∧ S.hT f (F.fvec a.succ) = 0 := by
    by_cases h : a.1 + 1 < r
    · have hs : a.succ = (⟨a.1 + 1, h⟩ : Fin r).castSucc := Fin.ext (by simp)
      have he : F.fvec a.succ = F.e ⟨a.1 + 1, h⟩ := by
        rw [FlagG.fvec, hs, Fin.snoc_castSucc]
      rw [he]
      refine ⟨?_, ?_⟩
      · have h1 := lie_Xa hY (j := a.1 + 1 + 1) h (e_mem_Xa F ⟨a.1 + 1, h⟩)
        simpa using h1
      · rw [hf, if_neg]
        intro hb
        have := congrArg Fin.val hb
        simp at this
    · have hs : a.succ = Fin.last r := Fin.ext (by simp; omega)
      have he : F.fvec a.succ = F.z := by simp [FlagG.fvec, hs]
      have hr : a.1 + 1 = r := by omega
      rw [he, hr, Xa_ge F le_rfl]
      exact ⟨hY.2.2 _ hzperp, hfz⟩
  rw [nexp_apply s hY, map_sum, Finset.sum_eq_single 1]
  · simp only [pow_one, map_smul, smul_eq_mul, Nat.factorial_one, Nat.cast_one, inv_one, map_one,
      one_mul]
    rw [hT_eq_coefX F f a hf (hXa1 hw)]
  · intro i _ hi1
    rw [map_smul, smul_eq_mul]
    refine mul_eq_zero_of_right _ ?_
    rcases i with _ | i
    · simpa using hfv
    · rw [pow_succ, Module.End.mul_apply]
      have hi : 1 ≤ i := by omega
      exact hT_Xa_zero F f a.1
        (fun b hb => by rw [hf b, if_neg (fun h => by subst h; exact lt_irrefl _ hb)])
        (Xa_mono F (by omega) (lie_pow_Xa hY i ha hw))
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Exp

end Formalism.L2.SG.NonRelPf

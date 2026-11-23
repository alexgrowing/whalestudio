import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.BaseCaseIdentities (OrdGE NoConst)

section Gen

variable {k : Type*} [Field k] {Z B : Type*}

structure Contr (Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)) : Prop where
  noConst : ∀ t, NoConst (Ψ t)
  contr : ∀ (t t' : B → MvPowerSeries Z k) (n : ℕ), NoConst t → NoConst t' →
    (∀ c, OrdGE (n + 1) (t c - t' c)) → ∀ b, OrdGE (n + 2) (Ψ t b - Ψ t' b)

namespace Contr

variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)

include H

theorem noConst_iterate {t : B → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst (Ψ^[n] t) := by
  cases n with
  | zero => simpa using ht
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact H.noConst _

theorem iterate_close {a b : B → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) (Ψ^[n] a c - Ψ^[n] b c) := by
  induction n with
  | zero =>
    intro c A hA
    simp only [Function.iterate_zero, id_eq, map_sub, ha c A hA, hb c A hA, sub_zero]
  | succ n ih =>
    intro c
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact H.contr _ _ n (H.noConst_iterate ha n) (H.noConst_iterate hb n) ih c

omit H in
theorem noConst_zero : NoConst (0 : B → MvPowerSeries Z k) := by
  intro c A _
  simp

def fixPt (_H : Contr Ψ) : B → MvPowerSeries Z k := fun c A => coeff A (Ψ^[A.degree] 0 c)

theorem coeff_iterate_zero (c : B) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A (Ψ^[n] 0 c) = coeff A (H.fixPt c) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : coeff A (H.fixPt c) = coeff A (Ψ^[A.degree] 0 c) := rfl
  have h1 := H.iterate_close (a := Ψ^[j] 0) (b := 0) (H.noConst_iterate noConst_zero j)
    noConst_zero A.degree c A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h1
  rw [Function.iterate_add_apply, e]
  exact h1

theorem fixPt_close (n : ℕ) (c : B) : OrdGE (n + 1) (H.fixPt c - Ψ^[n] 0 c) := by
  intro A hA
  rw [map_sub, ← H.coeff_iterate_zero c A (Nat.lt_succ_iff.mp hA), sub_self]

theorem noConst_fixPt : NoConst H.fixPt := by
  intro c A hA
  have h := H.fixPt_close 0 c A hA
  simpa using h

theorem fix_fixPt : Ψ H.fixPt = H.fixPt := by
  funext c
  ext A
  have h1 := H.contr H.fixPt (Ψ^[A.degree] 0) A.degree H.noConst_fixPt
    (H.noConst_iterate noConst_zero _) (fun c' => H.fixPt_close A.degree c') c A (by omega)
  rw [map_sub, sub_eq_zero, ← Function.iterate_succ_apply' Ψ A.degree 0] at h1
  rw [h1, H.coeff_iterate_zero c A (Nat.le_succ _)]

theorem exists_unique : ∃! t : B → MvPowerSeries Z k, NoConst t ∧ Ψ t = t := by
  refine ⟨H.fixPt, ⟨H.noConst_fixPt, H.fix_fixPt⟩, ?_⟩
  rintro t ⟨ht, hft⟩
  funext c
  ext A
  have h1 := H.iterate_close ht H.noConst_fixPt A.degree c A (Nat.lt_succ_self _)
  rw [Function.iterate_fixed hft, Function.iterate_fixed H.fix_fixPt, map_sub, sub_eq_zero] at h1
  exact h1

end Contr

theorem noConst_iff (t : B → MvPowerSeries Z k) :
    NoConst t ↔ ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := by
  constructor
  · intro h c
    have h0 := h c 0 (by simp)
    simpa using h0
  · intro h c A hA
    have hA0 : A.degree = 0 := by omega
    have hA1 : A = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff A).mp hA0
      | exact Finsupp.degree_eq_zero_iff.mp hA0
      | simpa using hA0
    subst hA1
    simpa using h c

end Gen

section Main

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}

namespace Sys

variable (S : Sys X)

def Mt : Matrix I I C := Matrix.of S.tan

theorem al_zero (c x : I) : S.al c 0 x = S.Mt c x := by
  have h := S.3 c
  unfold Cart.IsCurve at h
  unfold Sys.al
  rw [h.2.1]
  rfl

theorem det_ne : S.Mt.det ≠ 0 := by
  intro h
  have h5 := S.4
  change V.v S.Mt.det = 0 at h5
  rw [h, AddValuation.map_zero] at h5
  simp at h5

def Rr (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) : C :=
  ∑ s ∈ Finset.range μ.degree, ∑ c : I, S.al c (s + 1) x * coeff μ (t c ^ (V.l ^ (s + 1)))

def dl (x : I) (μ : I →₀ ℕ) : C := if μ = Finsupp.single x 1 then 1 else 0

def Ps (t : I → MvPowerSeries I C) : I → MvPowerSeries I C := fun c μ =>
  Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c

theorem coeff_Ps (t : I → MvPowerSeries I C) (c : I) (μ : I →₀ ℕ) :
    coeff μ (S.Ps t c) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c := rfl

theorem two_le_pow (s : ℕ) : 2 ≤ V.l ^ (s + 1) := by
  first
  | exact V.3.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero s) _)
  | exact le_trans V.3.two_le (Nat.le_self_pow (by omega) _)
  | calc 2 ≤ V.l := V.3.two_le
      _ = V.l ^ 1 := (pow_one _).symm
      _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right V.3.pos (by omega)

theorem contr : Contr S.Ps where
  noConst t c A hA := by
    have hA0 : A.degree = 0 := by omega
    rw [coeff_Ps]
    have : (fun x => dl x A - S.Rr t x A) = (0 : I → C) := by
      funext x
      have h1 : dl (C := C) x A = 0 := by
        unfold dl
        rw [if_neg]
        intro h
        rw [h, Finsupp.degree_single] at hA0
        omega
      have h2 : S.Rr t x A = 0 := by
        unfold Rr
        rw [hA0]
        simp
      simp [h1, h2]
    rw [this, Matrix.zero_vecMul]
    rfl
  contr t t' n ht ht' h b A hA := by
    rw [map_sub, coeff_Ps, coeff_Ps, sub_eq_zero]
    have : (fun x => dl x A - S.Rr t x A) = (fun x => dl x A - S.Rr t' x A) := by
      funext x
      congr 1
      unfold Rr
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
      have hN := two_le_pow (V := V) s
      have := Formalism.BaseCaseIdentities.OrdGE.pow_sub_pow (ht c) (ht' c) (h c) (N := V.l ^ (s + 1)) (by omega) A
        (by omega)
      rw [map_sub, sub_eq_zero] at this
      rw [this]
    rw [this]

theorem eqn_eq (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) :
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ c : I,
        S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))) =
      Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ := by
  rw [Finset.sum_range_succ', add_comm (Matrix.vecMul _ _ _)]
  congr 1
  all_goals first
    | rfl
    | (show _ = ∑ c, coeff μ (t c) * S.Mt c x
       exact Finset.sum_congr rfl fun c _ => by rw [S.al_zero c x, pow_zero, pow_one, mul_comm])

theorem isT_iff (t : I → MvPowerSeries I C) : S.IsT t ↔ NoConst t ∧ S.Ps t = t := by
  have hdet : IsUnit S.Mt.det := isUnit_iff_ne_zero.mpr S.det_ne
  have key : ∀ μ : I →₀ ℕ, ((∀ x, Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ = dl x μ) ↔
      (fun c => coeff μ (t c)) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹) := by
    intro μ
    constructor
    · intro h
      have h' : Matrix.vecMul (fun c => coeff μ (t c)) S.Mt = fun x => dl x μ - S.Rr t x μ := by
        funext x
        exact eq_sub_of_add_eq (h x)
      rw [← h', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    · intro h x
      rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      simp
  rw [Sys.IsT, noConst_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · funext c
    ext μ
    rw [S.coeff_Ps]
    have hk := (key μ).mp (fun x => by rw [← S.eqn_eq t x μ]; exact h x μ)
    exact (congrFun hk c).symm
  · intro x μ
    rw [S.eqn_eq t x μ]
    refine (key μ).mpr ?_ x
    funext c
    rw [← S.coeff_Ps, h]

end Sys

theorem tExistsUnique (X : Cart V d I J) : TExistsUnique X := by
  intro S
  obtain ⟨t, ⟨h1, h2⟩, hu⟩ := S.contr.exists_unique
  exact ⟨t, (S.isT_iff t).mpr ⟨h1, h2⟩, fun t' ht' => hu t' ((S.isT_iff t').mp ht')⟩

end Main

end Formalism.L2.FormalSeriesBounds

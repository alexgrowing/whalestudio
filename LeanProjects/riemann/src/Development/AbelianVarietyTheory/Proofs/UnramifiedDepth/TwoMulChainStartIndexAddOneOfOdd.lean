import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (Data Kn s0)
open Classical

noncomputable section

namespace GlobalTheory.MainTerm

variable {C : Type} [Field C]

def linPull {σ ι : Type} [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C) : MvPowerSeries ι C :=
  MvPowerSeries.subst (fun x : σ => ∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)) F

def chainMat {Z I : Type} [Fintype I] (D : Data C Z I) (s : ℕ) : I → I → C :=
  Nat.rec (motive := fun _ => I → I → C) (fun e c0 => if e = c0 then 1 else 0)
    (fun s p e c0 => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i),
      (D.l : C) * D.al c 2 e * p c c0 ^ (D.l ^ 2)) s

theorem chainMat_zero {Z I : Type} [Fintype I] (D : Data C Z I) (e c0 : I) :
    chainMat D 0 e c0 = if e = c0 then 1 else 0 := rfl

theorem chainMat_succ {Z I : Type} [Fintype I] (D : Data C Z I) (s : ℕ) (e c0 : I) :
    chainMat D (s + 1) e c0 = ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i),
      (D.l : C) * D.al c 2 e * chainMat D s c c0 ^ (D.l ^ 2) := rfl

variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

def mainVec {G : Cart V d I J} (S : Sys G) {Z : Type} (D : Data C Z I) (c0 : I) (κ : J) : C :=
  (-1) ^ (s0 D.i + 1) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s0 D.i ∧ s0 D.i < Kn D.i),
    chainMat D (s0 D.i) c c0 ^ D.l * ((D.l : C) * S.be c 1 κ)

def Adapted {G : Cart V d I J} (S : Sys G) {Z : Type} (D : Data C Z I) (a : ZMod d) (i : ℕ) : Prop :=
  D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
    (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
    (∀ c, D.lev c < Kn i → G.ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d))

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
theorem _root_.GlobalTheory.MainTerm.chainStartIndex_lt_chainLength_of_odd {i : ℕ} (hi : Odd i) : _root_.Formalism.BaseCaseIdentities.s0 i < _root_.Formalism.BaseCaseIdentities.Kn i := by
  obtain ⟨k, rfl⟩ := hi
  unfold _root_.Formalism.BaseCaseIdentities.s0 _root_.Formalism.BaseCaseIdentities.Kn
  omega

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
theorem _root_.GlobalTheory.MainTerm.two_mul_chainStartIndex_add_one_of_odd {i : ℕ} (hi : Odd i) : 2 * _root_.Formalism.BaseCaseIdentities.s0 i + 1 = i := by
  obtain ⟨k, rfl⟩ := hi
  unfold _root_.Formalism.BaseCaseIdentities.s0
  omega

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
theorem _root_.GlobalTheory.MainTerm.Kn_eq {i : ℕ} (hi : Odd i) :
    _root_.Formalism.BaseCaseIdentities.Kn i = _root_.Formalism.BaseCaseIdentities.s0 i + 1 := by
  obtain ⟨k, rfl⟩ := hi
  unfold _root_.Formalism.BaseCaseIdentities.s0 _root_.Formalism.BaseCaseIdentities.Kn
  omega

section

variable {G : Cart V d I J} {S : Sys G} {Z : Type} {D : Data C Z I} {a : ZMod d} {i : ℕ}

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.tan_int (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) (c x : I) : V.Ge 0 (S.tan c x) := by
  have h := G.bound0 0 (S.cur c) (S.mem c) (Sum.inl x)
  rw [S.cur_zero_inl] at h
  simpa using h

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.tan_pure (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) (c x : I)
    (h : G.ty (Sum.inl x) ≠ G.ty (Sum.inl c)) : S.tan c x = 0 := by
  rw [← S.cur_zero_inl]
  exact S.pure c 0 (Sum.inl x) (by simpa using h)

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.al_one
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) {c : I} (hc : D.good c) (x : I) : S.al c 1 x = 0 := by
  obtain ⟨-, -, -, hal, -⟩ := h
  rw [hal c 1 x le_rfl]
  simp [D.al_one c hc]

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.good (h : _root_.GlobalTheory.MainTerm.Adapted S D a i)
    {c : I} (hc : D.good c) :
    G.Good (G.ty (Sum.inl c)) (S.tan c) (S.cur c) := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.Cart.Good
  exact ⟨S.curve c, fun x => _root_.GlobalTheory.MainTerm.Adapted.al_one h hc x⟩

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.l_mul_al_two_int
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) {c : I} (hc : D.good c) (e : I) :
    V.Ge 0 ((D.l : C) * D.al c 2 e) := by
  obtain ⟨hv, hl, -, -, -⟩ := h
  have h2 := D.al_good c hc 2 e (by norm_num)
  have hge : V.Ge (-1) (D.al c 2 e) := by
    unfold _root_.Formalism.L2.FormalSeriesBounds.VF.Ge
    rw [← hv]
    refine le_trans (le_of_eq ?_) h2
    norm_num
  rw [hl]
  exact hge.l_mul.mono (by norm_num)

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.l_mul_be_one_int (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) (c : I) (κ : J) :
    V.Ge 0 ((V.l : C) * S.be c 1 κ) := by
  have h := G.bound0 1 (S.cur c) (S.mem c) (Sum.inr κ)
  exact h.l_mul.mono (by norm_num)

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.chainMat_int
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) (s : ℕ) (e c0 : I) :
    V.Ge 0 (_root_.GlobalTheory.MainTerm.chainMat D s e c0) := by
  induction s generalizing e with
  | zero =>
    rw [_root_.GlobalTheory.MainTerm.chainMat_zero]
    split_ifs
    · exact _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | succ s ih =>
    rw [_root_.GlobalTheory.MainTerm.chainMat_succ]
    refine _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun c hc => ?_
    rw [Finset.mem_filter] at hc
    have hgood : D.good c := D.pure_good c (by rw [hc.2.1]; exact hc.2.2)
    exact _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int
      (_root_.GlobalTheory.MainTerm.Adapted.l_mul_al_two_int h hgood e) ((ih c).pow _)

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.mainVec_int
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) (c0 : I) (κ : J) :
    V.Ge 0 (_root_.GlobalTheory.MainTerm.mainVec S D c0 κ) := by
  unfold _root_.GlobalTheory.MainTerm.mainVec
  refine _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int ((_root_.Formalism.L2.FormalSeriesBounds.VF.Ge.one (V := V)).neg.pow _)
    (_root_.Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun c _ => ?_)
  refine _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int
    ((_root_.GlobalTheory.MainTerm.Adapted.chainMat_int h _ c c0).pow _) ?_
  rw [h.2.1]
  exact _root_.GlobalTheory.MainTerm.l_mul_be_one_int S c κ

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.mainVec_pure
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) (c0 : I) (κ : J)
    (hκ : G.ty (Sum.inr κ) ≠ a + (i : ZMod d)) : _root_.GlobalTheory.MainTerm.mainVec S D c0 κ = 0 := by
  obtain ⟨-, -, hi, -, hty⟩ := h
  unfold _root_.GlobalTheory.MainTerm.mainVec
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hlev, hlt⟩ := hc
  have hodd : Odd i := hi ▸ D.i_odd
  have hc' := hty c (by rw [hlev, hi]; rwa [hi] at hlt)
  have h2 : ((i : ℕ) : ZMod d) = ((2 * _root_.Formalism.BaseCaseIdentities.s0 i + 1 : ℕ) : ZMod d) := by
    rw [_root_.GlobalTheory.MainTerm.two_mul_chainStartIndex_add_one_of_odd hodd]
  have hbe : S.be c 1 κ = 0 := by
    unfold _root_.Formalism.L2.FormalSeriesBounds.Sys.be
    apply S.pure c 1 (Sum.inr κ)
    rw [hc', hlev, hi]
    intro heq
    apply hκ
    rw [heq, h2]
    push_cast
    ring
  rw [hbe]
  simp

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in
theorem _root_.GlobalTheory.MainTerm.Adapted.mainVec_level_one
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a 1) {c0 : I} (hc : D.lev c0 = 0) (κ : J) :
    _root_.GlobalTheory.MainTerm.mainVec S D c0 κ = -((V.l : C) * S.be c0 1 κ) := by
  obtain ⟨-, hl, hi, -, -⟩ := h
  have hl0 : D.l ≠ 0 := by have := D.l_ge; omega
  unfold _root_.GlobalTheory.MainTerm.mainVec
  rw [hi]
  have hs : _root_.Formalism.BaseCaseIdentities.s0 1 = 0 := rfl
  have hk : _root_.Formalism.BaseCaseIdentities.Kn 1 = 1 := rfl
  rw [hs, hk, Finset.sum_eq_single c0]
  · simp [_root_.GlobalTheory.MainTerm.chainMat_zero, hl]
  · intro b _ hb
    simp [_root_.GlobalTheory.MainTerm.chainMat_zero, hb, zero_pow hl0]
  · intro hc0
    simp [hc] at hc0

open Classical in
variable {C : Type} [Field C] in
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] in
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ} in

theorem _root_.GlobalTheory.MainTerm.isSat_tan (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) {N : ℕ} (em : Fin N ↪ I) :
    _root_.Formalism.L2.FormalSeriesBounds.IsSat V (fun δ => S.tan (em δ)) := by
  have hu : V.v (Matrix.of S.tan).det = 0 := S.unimod
  have hdet : (Matrix.of S.tan).det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hu
    simp at hu
  have hint : ∀ x y, V.Ge 0 (Matrix.of S.tan x y) :=
    fun x y => _root_.GlobalTheory.MainTerm.tan_int S x y
  unfold _root_.Formalism.L2.FormalSeriesBounds.IsSat
  refine ⟨fun c x => _root_.GlobalTheory.MainTerm.tan_int S _ _,
    fun x c' => (Matrix.of S.tan)⁻¹ x (em c'),
    fun x c' => _root_.Formalism.L2.FormalSeriesBounds.inv_int (Matrix.of S.tan) hint hu x (em c'), fun c c' => ?_⟩
  have h1 := congrFun (congrFun
    (Matrix.mul_nonsing_inv (Matrix.of S.tan) (isUnit_iff_ne_zero.2 hdet)) (em c)) (em c')
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simpa [em.injective.eq_iff] using h1

end

end GlobalTheory.MainTerm

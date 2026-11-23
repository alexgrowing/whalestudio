import Mathlib
import Formalism.LocalRingCardinality.DataTheta

noncomputable section

namespace GlobalTheory.BranchTop

open Formalism.BasicNotions.TH

variable {R S : ℕ}

def lowP (r₀ : Fin R) (s₀ : Fin S) : Ix R S → Ix R S → Prop
  | .inl i, .inl k => i ≠ r₀ ∧ k = r₀
  | .inr j, .inr k => j ≠ s₀ ∧ k = s₀
  | _, _ => False

def raiseP (r₀ : Fin R) (s₀ : Fin S) : Ix R S → Ix R S → Prop
  | .inl i, .inl k => i = r₀ ∧ k ≠ r₀
  | .inr j, .inr k => j = s₀ ∧ k ≠ s₀
  | _, _ => False

def leviP (r₀ : Fin R) (s₀ : Fin S) : Ix R S → Ix R S → Prop
  | .inl i, .inl k => (i = r₀ ↔ k = r₀)
  | .inr j, .inr k => (j = s₀ ↔ k = s₀)
  | _, _ => False

def Supp (P : Ix R S → Ix R S → Prop) (X : Mat R S) : Prop := ∀ a b, ¬ P a b → X a b = 0

theorem supp_mul {P Q Z : Ix R S → Ix R S → Prop} (h : ∀ a k b, P a k → Q k b → Z a b)
    {X Y : Mat R S} (hX : Supp P X) (hY : Supp Q Y) : Supp Z (X * Y) := by
  intro a b hz
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hP : P a k
  · by_cases hQ : Q k b
    · exact absurd (h a k b hP hQ) hz
    · simp [hY k b hQ]
  · simp [hX a k hP]

theorem supp_sub {Z : Ix R S → Ix R S → Prop} {X Y : Mat R S} (hX : Supp Z X) (hY : Supp Z Y) :
    Supp Z (X - Y) := by
  intro a b hz
  simp [Matrix.sub_apply, hX a b hz, hY a b hz]

theorem supp_kc {P : Ix R S → Ix R S → Prop} (hP : ∀ a b, P a b → sameBlock a b) {X : Mat R S}
    (hX : Supp P X) : IsKC X :=
  fun a b hab => hX a b fun h => hab (hP a b h)

theorem supp_single {P : Ix R S → Ix R S → Prop} {a b : Ix R S} (h : P a b) : Supp P (Eab a b) := by
  intro c d hcd
  have : ¬ (a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩
    exact hcd h
  simp [Eab, Matrix.single_apply, this]

variable (r₀ : Fin R) (s₀ : Fin S)

theorem low_block : ∀ a b, lowP r₀ s₀ a b → sameBlock a b := by
  intro a b; cases a <;> cases b <;> simp [lowP, sameBlock]

theorem raise_block : ∀ a b, raiseP r₀ s₀ a b → sameBlock a b := by
  intro a b; cases a <;> cases b <;> simp [raiseP, sameBlock]

theorem levi_block : ∀ a b, leviP r₀ s₀ a b → sameBlock a b := by
  intro a b; cases a <;> cases b <;> simp [leviP, sameBlock]

theorem block_tri : ∀ a b, sameBlock a b → lowP r₀ s₀ a b ∨ raiseP r₀ s₀ a b ∨ leviP r₀ s₀ a b := by
  intro a b; cases a <;> cases b <;> simp only [lowP, raiseP, leviP, sameBlock] <;> tauto

theorem levi_low : ∀ a k b, leviP r₀ s₀ a k → lowP r₀ s₀ k b → lowP r₀ s₀ a b := by
  intro a k b; cases a <;> cases k <;> cases b <;> simp only [lowP, leviP] <;> tauto

theorem low_levi : ∀ a k b, lowP r₀ s₀ a k → leviP r₀ s₀ k b → lowP r₀ s₀ a b := by
  intro a k b; cases a <;> cases k <;> cases b <;> simp only [lowP, leviP] <;> tauto

theorem raise_low : ∀ a k b, raiseP r₀ s₀ a k → lowP r₀ s₀ k b → leviP r₀ s₀ a b := by
  intro a k b; cases a <;> cases k <;> cases b <;> simp only [lowP, leviP, raiseP] <;> tauto

theorem low_raise : ∀ a k b, lowP r₀ s₀ a k → raiseP r₀ s₀ k b → leviP r₀ s₀ a b := by
  intro a k b; cases a <;> cases k <;> cases b <;> simp only [lowP, leviP, raiseP] <;> tauto

theorem levi_cases : ∀ a b, leviP r₀ s₀ a b →
    (a = .inl r₀ ∧ b = .inl r₀) ∨ (a = .inr s₀ ∧ b = .inr s₀) ∨
    (sameBlock a b ∧ a ≠ .inl r₀ ∧ b ≠ .inl r₀ ∧ a ≠ .inr s₀ ∧ b ≠ .inr s₀) := by
  intro a b; cases a <;> cases b <;> simp only [leviP, sameBlock, ne_eq, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, not_false_eq_true, and_true, true_and, false_and, or_false,
    false_or] <;> tauto

theorem diag_comm {L : Mat R S} (hL : Supp (lowP r₀ s₀) L) :
    (Eab (.inl r₀) (.inl r₀) + Eab (.inr s₀) (.inr s₀)) * L -
      L * (Eab (.inl r₀) (.inl r₀) + Eab (.inr s₀) (.inr s₀)) = -L := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply, Eab]
  have hl : ∀ c : Ix R S, (Matrix.single c c (1:ℂ) * L) a b = if a = c then L a b else 0 := by
    intro c
    by_cases ha : a = c
    · subst ha; simp [Matrix.single_mul_apply_same]
    · simp [ha, Matrix.single_mul_apply_of_ne (h := ha)]
  have hr : ∀ c : Ix R S, (L * Matrix.single c c (1:ℂ)) a b = if b = c then L a b else 0 := by
    intro c
    by_cases hb : b = c
    · subst hb; simp [Matrix.mul_single_apply_same]
    · simp [hb, Matrix.mul_single_apply_of_ne (hbj := hb)]
  rw [hl, hl, hr, hr]
  by_cases hab : lowP r₀ s₀ a b
  · rcases a with i | j <;> rcases b with k | l <;> simp only [lowP] at hab
    · obtain ⟨hi, rfl⟩ := hab; simp [hi]
    · obtain ⟨hj, rfl⟩ := hab; simp [hj]
  · simp [hL a b hab]

section Mod

variable {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]

theorem mem_of_entries (P : Submodule ℂ V) (f : Mat R S →ₗ[ℂ] Module.End ℂ V) (X : Mat R S) (v : V)
    (h : ∀ a b, X a b ≠ 0 → f (Eab a b) v ∈ P) : f X v ∈ P := by
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : X a b = 0
  · simp [hab]
  · have e : Matrix.single a b (X a b) = X a b • Eab a b := by simp [Eab, Matrix.smul_single]
    rw [e, map_smul, LinearMap.smul_apply]
    exact P.smul_mem _ (h a b hab)

def subQ (act : ι → Mat R S →ₗ[ℂ] Module.End ℂ V) (Q : Mat R S → Prop) (M : Submodule ℂ V) :
    Submodule ℂ V :=
  M ⊓ ⨅ (w : ι) (X : Mat R S) (_ : Q X), M.comap (act w X)

theorem mem_subQ (act : ι → Mat R S →ₗ[ℂ] Module.End ℂ V) (Q : Mat R S → Prop) (M : Submodule ℂ V)
    (v : V) : v ∈ subQ act Q M ↔ v ∈ M ∧ ∀ w X, Q X → act w X v ∈ M := by
  simp [subQ, Submodule.mem_iInf]

theorem bracket_step (act : ι → Mat R S →ₗ[ℂ] Module.End ℂ V)
    (hLie : ∀ w X Y, IsKC X → IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X)
    (hComm : ∀ w w', w ≠ w' → ∀ X Y, IsKC X → IsKC Y → act w X * act w' Y = act w' Y * act w X)
    (Q Q' Low : Mat R S → Prop) (hQ : ∀ X, Q X → IsKC X) (hLow : ∀ L, Low L → IsKC L)
    (hbr : ∀ X L, Q X → Low L → Q' (X * L - L * X)) (M : Submodule ℂ V)
    (hM : ∀ w L, Low L → ∀ v ∈ M, act w L v ∈ M) (hM' : ∀ w Y, Q' Y → ∀ v ∈ M, act w Y v ∈ M) :
    ∀ w' L, Low L → ∀ v ∈ subQ act Q M, act w' L v ∈ subQ act Q M := by
  intro w' L hL v hv
  rw [mem_subQ] at hv ⊢
  refine ⟨hM w' L hL v hv.1, fun w X hX => ?_⟩
  by_cases hw : w = w'
  · subst hw
    have h := hLie w X L (hQ X hX) (hLow L hL)
    have e : act w X (act w L v) = act w L (act w X v) + act w (X * L - L * X) v := by
      rw [h]; simp [Module.End.mul_apply]
    rw [e]
    exact M.add_mem (hM w L hL _ (hv.2 w X hX)) (hM' w _ (hbr X L hX hL) v hv.1)
  · have h := hComm w w' hw X L (hQ X hX) (hLow L hL)
    have e : act w X (act w' L v) = act w' L (act w X v) := by
      rw [← Module.End.mul_apply, h, Module.End.mul_apply]
    rw [e]
    exact hM w' L hL _ (hv.2 w X hX)

end Mod

section Main

variable {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]

theorem top_step (act : ι → Mat R S →ₗ[ℂ] Module.End ℂ V)
    (hLie : ∀ w X Y, IsKC X → IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X)
    (hComm : ∀ w w', w ≠ w' → ∀ X Y, IsKC X → IsKC Y → act w X * act w' Y = act w' Y * act w X)
    (c c' : ι → ℂ) (T N M : Submodule ℂ V)
    (hT : ∀ v ∈ T, ∀ w, act w (Eab (.inl r₀) (.inl r₀)) v = c w • v ∧
      act w (Eab (.inr s₀) (.inr s₀)) v = c' w • v)
    (hNT : N ≤ T)
    (hmin : ∀ P : Submodule ℂ V, N ≤ P →
      (∀ w L, Supp (lowP r₀ s₀) L → ∀ v ∈ P, act w L v ∈ P) → M ≤ P)
    (hTM : T ≤ M) : T ≤ N := by
  classical
  set D : Mat R S := Eab (.inl r₀) (.inl r₀) + Eab (.inr s₀) (.inr s₀) with hD
  have hDkc : IsKC D := by
    intro a b hab
    have h1 : IsKC (Eab (.inl r₀) (.inl r₀) : Mat R S) :=
      supp_kc (levi_block r₀ s₀) (supp_single (P := leviP r₀ s₀) (by simp [leviP]))
    have h2 : IsKC (Eab (.inr s₀) (.inr s₀) : Mat R S) :=
      supp_kc (levi_block r₀ s₀) (supp_single (P := leviP r₀ s₀) (by simp [leviP]))
    simp [hD, Matrix.add_apply, h1 a b hab, h2 a b hab]
  set h : Module.End ℂ V := ∑ w, act w D with hh
  set C : ℂ := ∑ w, (c w + c' w) with hC
  have happ : ∀ x, h x = ∑ w, act w D x := by
    intro x; simp [hh, LinearMap.sum_apply]
  have hcomm : ∀ w L, Supp (lowP r₀ s₀) L → ∀ x (μ : ℂ), h x = μ • x →
      h (act w L x) = (μ - 1) • act w L x := by
    intro w L hL x μ hx
    have hLkc : IsKC L := supp_kc (low_block r₀ s₀) hL
    have hterm : ∀ w', act w' D (act w L x) =
        act w L (act w' D x) - (if w' = w then act w L x else 0) := by
      intro w'
      by_cases hw : w' = w
      · subst hw
        have e := hLie w' D L hDkc hLkc
        rw [diag_comm r₀ s₀ hL, map_neg] at e
        have e2 := congrArg (fun F : Module.End ℂ V => F x) e
        simp only [LinearMap.neg_apply, LinearMap.sub_apply, Module.End.mul_apply] at e2
        simp only [if_true]
        rw [eq_sub_iff_add_eq] at e2 ⊢
        rw [← e2]; abel
      · have e := hComm w' w hw D L hDkc hLkc
        simp only [hw, if_false, sub_zero]
        rw [← Module.End.mul_apply, e, Module.End.mul_apply]
    rw [happ, Finset.sum_congr rfl (fun w' _ => hterm w'), Finset.sum_sub_distrib,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← map_sum, ← happ, hx, map_smul, sub_smul,
      one_smul]
  have hTe : ∀ v ∈ T, h v = C • v := by
    intro v hv
    rw [happ, hC, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hD, map_add, LinearMap.add_apply, (hT v hv w).1, (hT v hv w).2, add_smul]
  set E : ℕ → Submodule ℂ V := fun k => Module.End.eigenspace h (C - ((k : ℂ) + 1)) with hE
  set Elow : Submodule ℂ V := ⨆ k, E k with hElow
  have hP : N ⊔ Elow = N ⊔ Elow := rfl
  have hstab : ∀ w L, Supp (lowP r₀ s₀) L → ∀ v ∈ N ⊔ Elow, act w L v ∈ N ⊔ Elow := by
    intro w L hL v hv
    obtain ⟨n, hn, e, he, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_right ?_)
    · refine (le_iSup E 0) ?_
      rw [hE, Module.End.mem_eigenspace_iff, hcomm w L hL n C (hTe n (hNT hn))]
      congr 1; push_cast; ring
    · refine Submodule.iSup_induction E (motive := fun x => act w L x ∈ Elow) he ?_ ?_ ?_
      · intro k x hx
        refine (le_iSup E (k + 1)) ?_
        rw [hE, Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hcomm w L hL x _ hx]
        congr 1; push_cast; ring
      · simp
      · intro x y hx hy
        rw [map_add]; exact Submodule.add_mem _ hx hy
  have hsub : Elow ≤ ⨆ μ, ⨆ (_ : μ ≠ C), Module.End.eigenspace h μ := by
    refine iSup_le fun k => ?_
    refine le_iSup₂_of_le (f := fun μ (_ : μ ≠ C) => Module.End.eigenspace h μ)
      (C - ((k : ℂ) + 1)) ?_ le_rfl
    intro heq
    have : ((k : ℂ) + 1) = 0 := by linear_combination -heq
    exact absurd this (by exact_mod_cast Nat.succ_ne_zero k)
  have hdis := (Module.End.eigenspaces_iSupIndep h) C
  intro v hv
  obtain ⟨n, hn, e, he, hne⟩ := Submodule.mem_sup.1 (hmin _ le_sup_left hstab (hTM hv))
  have he' : e ∈ Module.End.eigenspace h C := by
    have : e = v - n := by rw [← hne]; abel
    rw [this, Module.End.mem_eigenspace_iff, map_sub, hTe v hv, hTe n (hNT hn), smul_sub]
  have h0 : e = 0 := (Submodule.disjoint_def.1 hdis) e he' (hsub he)
  rw [← hne, h0, add_zero]
  exact hn

end Main

theorem top_irreducible : ∀ {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S)
    (act : ι → Formalism.BasicNotions.TH.Mat R S →ₗ[ℂ] Module.End ℂ V),
    (∀ w X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X) →
    (∀ w w', w ≠ w' → ∀ X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w X * act w' Y = act w' Y * act w X) →
    ∀ U : Submodule ℂ V, (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ U, act w X v ∈ U) →
    (∀ N : Submodule ℂ V, N ≤ U → (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ N, act w X v ∈ N) → N = ⊥ ∨ N = U) →
    ∀ (c c' : ι → ℂ) (T : Submodule ℂ V),
    (∀ v, v ∈ T ↔ v ∈ U ∧ ∀ w, act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧
      act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) →
    (∀ v ∈ T, ∀ w, (∀ i, i ≠ r₀ → act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
      ∀ j, j ≠ s₀ → act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) →
    ∀ N : Submodule ℂ V, N ≤ T →
    (∀ w X, Formalism.BasicNotions.TH.IsKC X → (∀ a, X a (.inl r₀) = 0 ∧ X (.inl r₀) a = 0 ∧ X a (.inr s₀) = 0 ∧ X (.inr s₀) a = 0) →
      ∀ v ∈ N, act w X v ∈ N) →
    N = ⊥ ∨ N = T := by
  intro ι V _ _ _ R S r₀ s₀ act hLie hComm U hU hIrr c c' T hTdef hTkill N hNT hk1
  classical
  have hTU : T ≤ U := fun v hv => ((hTdef v).1 hv).1
  have hT : ∀ v ∈ T, ∀ w, act w (Eab (.inl r₀) (.inl r₀)) v = c w • v ∧
      act w (Eab (.inr s₀) (.inr s₀)) v = c' w • v := fun v hv => ((hTdef v).1 hv).2
  let Low : Mat R S → Prop := Supp (lowP r₀ s₀)
  let Levi : Mat R S → Prop := Supp (leviP r₀ s₀)
  let Raise : Mat R S → Prop := Supp (raiseP r₀ s₀)
  have hLowKC : ∀ L, Low L → IsKC L := fun L hL => supp_kc (low_block r₀ s₀) hL
  have hLeviKC : ∀ L, Levi L → IsKC L := fun L hL => supp_kc (levi_block r₀ s₀) hL
  have hRaiseKC : ∀ L, Raise L → IsKC L := fun L hL => supp_kc (raise_block r₀ s₀) hL
  let 𝒮 : Set (Submodule ℂ V) := {P | N ≤ P ∧ ∀ w L, Low L → ∀ v ∈ P, act w L v ∈ P}
  let M : Submodule ℂ V := sInf 𝒮
  have hmin : ∀ P : Submodule ℂ V, N ≤ P → (∀ w L, Low L → ∀ v ∈ P, act w L v ∈ P) → M ≤ P :=
    fun P h1 h2 => sInf_le ⟨h1, h2⟩
  have hNM : N ≤ M := le_sInf fun P hP => hP.1
  have hMlow : ∀ w L, Low L → ∀ v ∈ M, act w L v ∈ M := by
    intro w L hL v hv
    rw [Submodule.mem_sInf] at hv ⊢
    intro P hP
    exact hP.2 w L hL v (hv P hP)

  have hNlevi : ∀ w X, Levi X → ∀ v ∈ N, act w X v ∈ N := by
    intro w X hX v hv
    refine mem_of_entries N (act w) X v fun a b hab => ?_
    have hl : leviP r₀ s₀ a b := by
      by_contra hn; exact hab (hX a b hn)
    rcases levi_cases r₀ s₀ a b hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hsb, h1, h2, h3, h4⟩
    · rw [(hT v (hNT hv) w).1]; exact N.smul_mem _ hv
    · rw [(hT v (hNT hv) w).2]; exact N.smul_mem _ hv
    · refine hk1 w (Eab a b) (supp_kc (P := fun x y => x = a ∧ y = b)
          (by rintro x y ⟨rfl, rfl⟩; exact hsb) (supp_single ⟨rfl, rfl⟩)) (fun d => ?_) v hv
      simp only [Eab, Matrix.single_apply]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h1, h2, h3, h4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

  have hMlevi : ∀ w Y, Levi Y → ∀ v ∈ M, act w Y v ∈ M := by
    have hle : M ≤ subQ act Levi M := by
      refine hmin _ (fun v hv => (mem_subQ act Levi M v).2
        ⟨hNM hv, fun w X hX => hNM (hNlevi w X hX v hv)⟩) ?_
      exact bracket_step act hLie hComm Levi Low Low hLeviKC hLowKC
        (fun X L hX hL => supp_sub (supp_mul (levi_low r₀ s₀) hX hL) (supp_mul (low_levi r₀ s₀) hL hX))
        M hMlow hMlow
    intro w Y hY v hv
    exact ((mem_subQ act Levi M v).1 (hle hv)).2 w Y hY

  have hMraise : ∀ w Y, Raise Y → ∀ v ∈ M, act w Y v ∈ M := by
    have hle : M ≤ subQ act Raise M := by
      refine hmin _ (fun v hv => (mem_subQ act Raise M v).2 ⟨hNM hv, fun w X hX => ?_⟩) ?_
      · refine mem_of_entries M (act w) X v fun a b hab => ?_
        have hr : raiseP r₀ s₀ a b := by
          by_contra hn; exact hab (hX a b hn)
        rcases a with i | j <;> rcases b with k | l <;> simp only [raiseP] at hr
        · obtain ⟨rfl, hk⟩ := hr
          rw [(hTkill v (hNT hv) w).1 k hk]; exact M.zero_mem
        · obtain ⟨rfl, hl⟩ := hr
          rw [(hTkill v (hNT hv) w).2 l hl]; exact M.zero_mem
      · exact bracket_step act hLie hComm Raise Levi Low hRaiseKC hLowKC
          (fun X L hX hL => supp_sub (supp_mul (raise_low r₀ s₀) hX hL)
            (supp_mul (low_raise r₀ s₀) hL hX))
          M hMlow hMlevi
    intro w Y hY v hv
    exact ((mem_subQ act Raise M v).1 (hle hv)).2 w Y hY

  have hMkc : ∀ w X, IsKC X → ∀ v ∈ M, act w X v ∈ M := by
    intro w X hX v hv
    refine mem_of_entries M (act w) X v fun a b hab => ?_
    have hsb : sameBlock a b := by
      by_contra hn; exact hab (hX a b hn)
    rcases block_tri r₀ s₀ a b hsb with h | h | h
    · exact hMlow w _ (supp_single h) v hv
    · exact hMraise w _ (supp_single h) v hv
    · exact hMlevi w _ (supp_single h) v hv
  have hMU : M ≤ U := hmin U (hNT.trans hTU) fun w L hL v hv => hU w L (hLowKC L hL) v hv
  rcases hIrr M hMU hMkc with h0 | hMeq
  · left; exact eq_bot_iff.2 (h0 ▸ hNM)
  · right
    refine le_antisymm hNT ?_
    exact top_step r₀ s₀ act hLie hComm c c' T N M hT hNT hmin (hMeq ▸ hTU)

end GlobalTheory.BranchTop

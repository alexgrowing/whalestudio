import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

section Basics

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem fvec_castSucc (F : FlagG S r T) (k : Fin r) : F.fvec k.castSucc = F.e k := by
  simp [FlagG.fvec]

theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi h : i.1 < b))

theorem e_mem_Xa (F : FlagG S r T) {k : Fin r} {a : ℕ} (hk : k.val < a) : F.e k ∈ F.Xa a := Submodule.subset_span ⟨k, hk, rfl⟩

theorem Xa_r (F : FlagG S r T) : F.Xa r = F.X := by
  simp [FlagG.Xa, FlagG.X]

theorem fXa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := Submodule.span_mono (Set.image_subset_range _ _)

theorem fe_mem_X (F : FlagG S r T) (k : Fin r) : F.e k ∈ F.X := Submodule.subset_span (Set.mem_range_self k)

theorem hT_Xa_of (F : FlagG S r T) (v : S.V) (a : ℕ)
    (hv : ∀ j : Fin r, j.val < a → S.hT v (F.e j) = 0) : ∀ y ∈ F.Xa a, S.hT v y = 0 := by
  have h1 : F.Xa a ≤ LinearMap.ker (S.hT v) :=
    Submodule.span_le.2 (by rintro _ ⟨j, hj, rfl⟩; exact hv j hj)
  intro y hy
  exact LinearMap.mem_ker.1 (h1 hy)

theorem hT_e_X (F : FlagG S r T) (j : Fin r) : ∀ y ∈ F.X, S.hT (F.e j) y = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT (F.e j)) :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact F.e_iso j k)
  intro y hy
  exact LinearMap.mem_ker.1 (h1 hy)

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT.flip y) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hT_e_X F j y hy)
  simpa using h1 hx

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT.flip F.z) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact F.z_orth j)
  simpa using h1 hx

theorem hT_X_fvec (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) (m : Fin (r + 1)) :
    S.hT x (F.fvec m) = 0 := by
  induction m using Fin.lastCases with
  | last => rw [fvec_last]; exact hT_X_alt F hx
  | cast k => rw [fvec_castSucc]; exact hT_X_X F hx (fe_mem_X F k)

theorem fvec_indep (F : FlagG S r T) (hT0 : T ≠ 0) : LinearIndependent E F.fvec := by
  rw [FlagG.fvec, linearIndependent_fin_snoc]
  refine ⟨F.e_indep, fun hz => hT0 ?_⟩
  have h1 := hT_X_alt F hz
  rw [F.z_norm] at h1
  exact neg_eq_zero.1 h1

theorem fvec_mem_Xa (F : FlagG S r T) (m : Fin (r + 1)) (hm : m.val < r) :
    F.fvec m ∈ F.Xa (m.val + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin r, k.castSucc = m := ⟨⟨m.val, hm⟩, rfl⟩
  rw [fvec_castSucc]
  exact e_mem_Xa F (Nat.lt_succ_self _)

end Basics

section TwoFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem Xa_le_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) (a : ℕ) : F'.Xa a ≤ F.Xa a := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k.1 < a := hk
  have h := hs k.castSucc
  rw [fvec_castSucc, fvec_castSucc] at h
  have h2 := Submodule.add_mem _ (Xa_mono F (le_of_lt hk') h)
    (Submodule.smul_mem _ (c k.castSucc) (e_mem_Xa F hk'))
  simpa using h2

theorem le_Xa_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) :
    ∀ a : ℕ, a ≤ r → F.Xa a ≤ F'.Xa a ∧ ∀ k : Fin r, k.val < a → c k.castSucc ≠ 0
  | 0, _ => by
    refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    have h0 : F.Xa 0 = ⊥ := by simp [FlagG.Xa]
    rw [h0]
    exact bot_le
  | a + 1, ha => by
    obtain ⟨ih1, ih2⟩ := le_Xa_of_same F F' c hs a (by omega)
    obtain ⟨ka, hka⟩ : ∃ ka : Fin r, ka.val = a := ⟨⟨a, by omega⟩, rfl⟩
    have hsa := hs ka.castSucc
    rw [fvec_castSucc, fvec_castSucc, Fin.val_castSucc, hka] at hsa
    have hmem : F'.e ka - c ka.castSucc • F.e ka ∈ F'.Xa a := ih1 hsa
    have hc : c ka.castSucc ≠ 0 := by
      intro h0
      rw [h0, zero_smul, sub_zero] at hmem
      exact F'.e_indep.notMem_span_image (s := {i : Fin r | i.val < a}) (x := ka)
        (by simp [hka]) hmem
    refine ⟨?_, ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, hk, rfl⟩
      have hk' : k.val < a + 1 := hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
      · exact Xa_mono F' (Nat.le_succ a) (ih1 (e_mem_Xa F h))
      · have hkk : k = ka := Fin.ext (h.trans hka.symm)
        subst hkk
        have h1 : F'.e k ∈ F'.Xa (a + 1) := e_mem_Xa F' (by omega)
        have h2 := Xa_mono F' (Nat.le_succ a) hmem
        have h3 := Submodule.smul_mem _ (c k.castSucc)⁻¹ (sub_mem h1 h2)
        rwa [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact ih2 k h
      · have hkk : k = ka := Fin.ext (h.trans hka.symm)
        rw [hkk]
        exact hc

theorem Xa_eq_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) (a : ℕ) (ha : a ≤ r) : F'.Xa a = F.Xa a := le_antisymm (Xa_le_of_same F F' c hs a) ((le_Xa_of_same F F' c hs a ha).1)

theorem X_eq_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) : F'.X = F.X := by
  rw [← Xa_r, ← Xa_r]
  exact Xa_eq_of_same F F' c hs r le_rfl

theorem c_ne_zero_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) (k : Fin r) : c k.castSucc ≠ 0 := (le_Xa_of_same F F' c hs r le_rfl).2 k k.2

end TwoFlags

end PI.FRS

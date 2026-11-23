import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem tie_Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  Submodule.span_mono (by rintro _ ⟨i, hi, rfl⟩; exact ⟨i, lt_of_lt_of_le hi h, rfl⟩)

theorem tie_e_mem_Xa (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) :=
  Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem tie_Xa_eq (F : FlagG S r T) (F' : FlagG S r T') (h : ∀ a, F'.e a - F.e a ∈ F.Xa a.val) (j : ℕ) :
    F'.Xa j = F.Xa j := by
  have h1 : ∀ j, F'.Xa j ≤ F.Xa j := by
    intro j
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F'.e a = (F'.e a - F.e a) + F.e a := by abel
    rw [h2]
    exact Submodule.add_mem _ (tie_Xa_mono F (le_of_lt ha) (h a)) (tie_Xa_mono F ha (tie_e_mem_Xa F a))
  refine le_antisymm (h1 j) ?_
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F.e a = F'.e a - (F'.e a - F.e a) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (tie_Xa_mono F' ha (tie_e_mem_Xa F' a))
      (tie_Xa_mono F' (le_of_lt ha) (ih a.val ha (h a)))

theorem tie_X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.X FlagG.Xa
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, a.isLt, rfl⟩
  · rintro ⟨a, _, rfl⟩; exact ⟨a, rfl⟩

end Gen

section Rec

variable {D : D7}

theorem tie_inS_sameFlag (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.inS t) :
    FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) := by
  obtain ⟨h1, h2⟩ := (X.inS_iff t).1 h
  have hXa := tie_Xa_eq (X.fl t).fl (X.fl' t).fl h1
  refine ⟨hXa, ?_⟩
  have hX : (X.fl' t).fl.X = (X.fl t).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  show (X.fl' t).fl.X ⊔ Submodule.span D.host.E {(X.fl' t).fl.z} =
    (X.fl t).fl.X ⊔ Submodule.span D.host.E {(X.fl t).fl.z}
  rw [hX]
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have : (X.fl' t).fl.z = ((X.fl' t).fl.z - (X.fl t).fl.z) + (X.fl t).fl.z := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h2)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_left (Submodule.span_le.2 ?_)
    rintro _ rfl
    have : (X.fl t).fl.z = (X.fl' t).fl.z - ((X.fl' t).fl.z - (X.fl t).fl.z) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_left h2)

theorem clause_a_of_identity_flag (X : TermTie D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hI : UnitaryVolumeMass.cIdFlag D X) :
    FrobeniusProjectedBounds.IntegralityFromMetric D large₂ X C' Cl Cg cb Cu cT CT C0 := by
  rintro ⟨_, a8, a9⟩ hH u
  have hirr := a8 hH u u
  have hid := a9 hH u
  have c4 : ∀ t : D.s.Term u u, FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) → D.s.relevant t → D.s.isId t :=
    fun t h => hI u t h
  have c3 : ∀ t : D.s.Term u u, D.s.inS t → D.s.relevant t → D.s.isId t :=
    fun t h => c4 t (tie_inS_sameFlag X t h)
  refine ⟨?_, fun t => tie_isId_inS X t, c3, c4, hirr, fun t => term_in_S_vanishes X t, ?_, S0ge1_of_tie X u u⟩
  ·
    let ι : {t : D.s.Term u u // D.s.isId t} → {t : D.s.Term u u // D.s.inS t} :=
      fun t => ⟨t.1, tie_isId_inS X t.1 t.2⟩
    have hinj : Function.Injective ι := fun a b h => Subtype.ext (congrArg (fun z => z.1) h)
    refine (hinj.hasSum_iff (f := fun t : {t : D.s.Term u u // D.s.inS t} => D.s.aTerm u u t.1) ?_).1 hid
    intro t ht
    apply hirr
    intro hr
    exact ht ⟨⟨t.1, c3 t.1 t.2 hr⟩, rfl⟩
  · unfold FrobeniusProjectedBounds.Kpp KOf
    rw [tsum_subtype, tsum_subtype]
    congr 1
    funext t
    classical
    by_cases hr : D.s.relevant t
    · have hiff : t ∈ {t : D.s.Term u u | D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t)} ↔
          t ∈ {t : D.s.Term u u | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} := by
        constructor
        · rintro ⟨_, hG, hS⟩
          exact ⟨hG, fun h => hS (tie_inS_sameFlag X t (tie_isId_inS X t h))⟩
        · rintro ⟨hG, hn⟩
          exact ⟨hr, hG, fun h => hn (c4 t h hr)⟩
      by_cases hm : t ∈ {t : D.s.Term u u | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.1 h))]
    · have h0 := hirr t hr
      simp only [Set.indicator_apply, h0, ite_self]

end Rec

end Formalism.MainNotions.BridgeLemma

end

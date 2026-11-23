import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation

noncomputable section

open Module Matrix
open Formalism.MainNotions.S Formalism.BasicNotions

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def Asp (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V :=
  Submodule.span E (Set.range (Sum.elim F.fvec F'.fvec))

def Hsp (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V := Lat.orth S (Asp F F')

theorem fvec_mem_Asp (F : FlagG S r T) (F' : FlagG S r T') (a : Fin (r + 1)) : F.fvec a ∈ Asp F F' :=
  Submodule.subset_span ⟨Sum.inl a, rfl⟩

theorem fvec'_mem_Asp (F : FlagG S r T) (F' : FlagG S r T') (a : Fin (r + 1)) : F'.fvec a ∈ Asp F F' :=
  Submodule.subset_span ⟨Sum.inr a, rfl⟩

theorem X_le_Asp (F : FlagG S r T) (F' : FlagG S r T') : F.X ≤ Asp F F' := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have := fvec_mem_Asp F F' (Fin.castSucc a)
  simpa [FlagG.fvec, Fin.snoc_castSucc] using this

theorem z_mem_Asp (F : FlagG S r T) (F' : FlagG S r T') : F.z ∈ Asp F F' := by
  have := fvec_mem_Asp F F' (Fin.last r)
  simpa [FlagG.fvec, Fin.snoc_last] using this

theorem Asp_symm (F : FlagG S r T) (F' : FlagG S r T') : Asp F' F = Asp F F' := by
  unfold Asp
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem hT_A_H {F : FlagG S r T} {F' : FlagG S r T'} {a w : S.V} (ha : a ∈ Asp F F') (hw : w ∈ Hsp F F') :
    S.hT a w = 0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hw a ha

theorem hT_H_A {F : FlagG S r T} {F' : FlagG S r T'} {a w : S.V} (ha : a ∈ Asp F F') (hw : w ∈ Hsp F F') :
    S.hT w a = 0 := by rw [hT_swap, hT_A_H ha hw, star_zero]

theorem finrank_Asp (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    finrank E (Asp F F') = 2 * r + 2 := by
  rw [Asp, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F F' hG), Fintype.card_sum, Fintype.card_fin]
  ring

theorem Asp_inf_Hsp (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) : Asp F F' ⊓ Hsp F F' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxH⟩ := Submodule.mem_inf.1 hx
  exact (Submodule.mem_bot E).2 (CorankRelation.span_pair_orth_eq_zero F F' hG x hxA fun i =>
    (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hxH _ (Submodule.subset_span ⟨i, rfl⟩))

theorem finrank_Hsp (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    finrank E (Hsp F F') + (2 * r + 2) = finrank E S.V := by
  have := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (Asp F F')
  rw [finrank_Asp F F' hG] at this
  exact this

theorem isCompl_AH (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    IsCompl (Asp F F') (Hsp F F') := by
  refine ⟨disjoint_iff.2 (Asp_inf_Hsp F F' hG), codisjoint_iff.2 ?_⟩
  refine Submodule.eq_top_of_finrank_eq ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Asp F F') (Hsp F F')
  rw [Asp_inf_Hsp F F' hG, finrank_bot, add_zero, finrank_Asp F F' hG] at h1
  have h2 := finrank_Hsp F F' hG
  omega

end Formalism.L2.SG.NGCut.NormalVectorPairings

import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Sg

open GlobalTheory.LvT.WtSign Formalism.MainNotions.product_first_zeroth_parts

theorem baseSigns_of_val (X : Stages) (L : SizeData₂ X.toD7) {C : FC} {cD ch : ℝ} (h : Val C cD ch L) :
    GlobalTheory.LvT.WtSign.BaseSigns X.B := by
  have hS : SignLaw X.toD7.hc (· ∈ tops X.toD7) := by
    refine ⟨uLast_le L, fun τ => ?_⟩
    by_cases hτ : τ ∈ tops X.toD7
    · exact eFirst_ge_of_uLast_le _ (uLast_le L τ hτ)
    · apply eFirst_ge_of_uLast_nonpos
      have hk : 0 < X.toD7.R.k := lt_of_lt_of_le (m_pos X.toD7.R) (by have := X.toD7.R.m_add_three_le_k; omega)
      have h1 := (h.hc.2.1 τ hk (fun h' => hτ ((mem_tops τ).2 h'))).2
      unfold uLast
      rw [h1]
      norm_num
  have e : ∀ τ, τ ∈ tops X.toD7 ↔ τ ∈ X.B.wts.tops := fun τ =>
    (mem_tops (D := assemble X.B X.C X.W X.V X.S X.N X.G) τ).trans (X.B.mem_wts_tops τ).symm
  exact ⟨fun τ hτ => hS.1 τ ((e τ).2 hτ), hS.2⟩

theorem baseSigns_of_bPt : ∀ (K : Ctx) (β : BPt K), GlobalTheory.LvT.WtSign.BaseSigns β.X.B :=
  fun _ β => baseSigns_of_val β.X β.p.L β.val

end GlobalTheory.Fc.Sg

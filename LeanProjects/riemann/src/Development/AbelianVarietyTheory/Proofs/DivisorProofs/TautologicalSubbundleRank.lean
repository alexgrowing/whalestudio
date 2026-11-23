import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStalkColumnSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagPointStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagStalkSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameMembershipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExistsStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem exists_mem_cellOpen (ι : Type) [Fintype ι] (N : ℕ) (y : Fl ι N) :
    ∃ w : ι → Equiv.Perm (Fin N), y ∈ cellOpen ι N w := by
  obtain ⟨w, hw⟩ := GlobalTheory.FlagZ.exists_mem_range_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd y
  exact ⟨w, (mem_cellOpen ι N).2 hw⟩

theorem mem_sub_iff_cellCol (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (w : ι → Equiv.Perm (Fin N))
    (V : (Fl ι N).Opens) (h : V ≤ cellOpen ι N w) (a : Fin N → Γ(Fl ι N, V)) :
    (∑ j, a j • resM _ h (cellCol ι N w τ j)) ∈ (sub ι N τ l).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 :=
  GlobalTheory.T.subbundle_frame_membership _ (GlobalTheory.T.cell_columns_frame ι N w τ) _ _
    (fun y hy => (GlobalTheory.T.flag_stalk_column_span ι N τ l y _ (GlobalTheory.T.cell_flag_point_stalk ι N w y hy)).trans (GlobalTheory.T.cell_flag_stalk_span ι N w τ l y hy)) h a

theorem isVB_F_and_isSubbundle_incl : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (i : Fin (N + 1)),
    VB.IsVB (F ι N τ i) i ∧ VB.IsSubbundle (incl ι N τ i) := by
  intro ι _ N τ i
  refine ⟨fun y => ?_, ⟨?_, N - i, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_mem_cellOpen ι N y
    obtain ⟨e, he⟩ := GlobalTheory.T.subbundle_frame_exists (sub ι N τ i) _ (GlobalTheory.T.cell_columns_frame ι N w τ) i i.is_le
      (mem_sub_iff_cellCol ι N τ i w)
    exact ⟨_, e, hw, he⟩
  · exact @mono_comp _ _ _ _ _ _ (VB.Sub.mono_incl _) _ inferInstance
  · refine (show VB.IsVB (cokernel (sub ι N τ i).incl) (N - i) from fun y => ?_).of_iso
      (cokernelCompIsIso _ _).symm
    obtain ⟨w, hw⟩ := exists_mem_cellOpen ι N y
    obtain ⟨e, he⟩ := GlobalTheory.T.quotient_bundle_frame_exists (sub ι N τ i) _ (GlobalTheory.T.cell_columns_frame ι N w τ) i i.is_le
      (mem_sub_iff_cellCol ι N τ i w)
    exact ⟨_, e, hw, he⟩

end GlobalTheory.FlagZ.Univ

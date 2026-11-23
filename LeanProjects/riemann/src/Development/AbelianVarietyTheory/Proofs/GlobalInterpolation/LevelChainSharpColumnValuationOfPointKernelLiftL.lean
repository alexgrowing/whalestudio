import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsStableOfTgtEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainUOperatorCommutationOfPointPairLaw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExtInOfValIn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfStability
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

theorem levelChainSharpColumnValuation_of_pointKernelLiftLaws (X : Ch D u) (Lv : LevTie X) (Vt : ValTie Lv) (Kt : KerTie Lv) (hK : KerLaws Vt Kt)
    (hS : StabUnit X) (hW : WtSigns X) : Conclusion5Sharp X := by
  have hB : WtBounds X := wtBounds_of_nonneg D u X hW.1 hW.2
  exact levelChainSharpColumnValuation_of_stability D u X (formsStable_of_tgtEq D u X Lv Kt hK.tgt)
    (levelChainUOperatorCommutation_of_pointPairLaw D u X Lv Kt hK.tgt hK.uk) (UKS.ukSharp D u X Lv Vt Kt hK hS hB) hB

private theorem Fi_zero_eq_span_range_emb (Z : Ch D u) :
    Z.fm.Fi 0 = Submodule.span ℂ (Set.range (Z.fm.emb 0)) := by
  apply le_antisymm
  · rw [← (Z.fm.emb_basis 0).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact emb_mem_Fi Z 0 x

private theorem mem_Fi_zero_iff_of_shared {X Y : Ch D u} {e : Fn X 0 ≃ₗ[ℂ] Fn Y 0} {eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0}
    (h : Shared X Y e eL) (φ : Fn X 0) : e φ ∈ Y.fm.Fi 0 ↔ φ ∈ X.fm.Fi 0 := by
  obtain ⟨ev, eF, hs⟩ := h
  have hmap : Y.fm.Fi 0 = (X.fm.Fi 0).map (e : Fn X 0 →ₗ[ℂ] Fn Y 0) := by
    rw [Fi_zero_eq_span_range_emb, Fi_zero_eq_span_range_emb, Submodule.map_span]
    congr 1
    ext ψ
    constructor
    · rintro ⟨y, rfl⟩
      have hy := hs.emb_eq (eL.symm y)
      rw [eL.apply_symm_apply] at hy
      exact ⟨X.fm.emb 0 (eL.symm y), ⟨_, rfl⟩, hy.symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eL x, hs.emb_eq x⟩
  rw [hmap]
  constructor
  · rintro ⟨ψ, hψ, hψe⟩
    rwa [← e.injective hψe]
  · intro hφ
    exact ⟨φ, hφ, rfl⟩

theorem step0Tie_of_twTie (Tw : TwForms D) (μ : D.what₂.Tup) (h : TwTie Tw u μ) (hU : UComm (own D u)) :
    Step0Tie Tw u μ := by
  intro w hw
  obtain ⟨ev, eF, hs⟩ := h
  have hwo : OverT (own D u) w := (hs.overT_iff w).1 ((OverT_tw Tw μ w).2 hw)
  refine ⟨hs.seen_eq w hwo, fun x hx => ?_⟩
  exact (TwTie.Nlam_iff ⟨ev, eF, hs⟩ hU hw x).2 hx

theorem uComm_own_of_twTie (Tw : TwForms D) (μ : D.what₂.Tup) (h : TwTie Tw u μ) (hU : UComm (tw Tw u μ)) :
    UComm (own D u) := by
  have hF := mem_Fi_zero_iff_of_shared h
  obtain ⟨ev, eF, hs⟩ := h

  have hmem : ∀ v, ∀ φ ∈ (own D u).fm.Fi 0, Uop (own D u) 0 v φ ∈ (own D u).fm.Fi 0 := by
    intro v φ hφ
    rw [← hF, hs.U_eq v φ hφ]
    exact hU.1 _ _ ((hF φ).2 hφ)
  refine ⟨hmem, fun v v' hvv' φ hφ => (D.e0Tw u μ).injective ?_⟩
  rw [hs.U_eq v _ (hmem v' φ hφ), hs.U_eq v' φ hφ, hs.U_eq v' _ (hmem v φ hφ), hs.U_eq v φ hφ]
  exact hU.2 _ _ (fun he => hvv' (ev.injective he)) _ ((hF φ).2 hφ)

theorem tuple_chain_sharp_column_valuation (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup)
    (Lv : LevTie (tw Tw u μ)) (Vt : ValTie Lv) (Kt : KerTie Lv) (hK : KerLaws Vt Kt)
    (hS : StabUnit (tw Tw u μ)) (hW : WtSigns (tw Tw u μ)) (h0 : Step0Tie Tw u μ) : TupleChainSharpColumnValuation Tw u μ :=
  TwSharp.tupleChainSharpColumnValuation_of_twisted D u Tw μ h0 (levelChainSharpColumnValuation_of_pointKernelLiftLaws (tw Tw u μ) Lv Vt Kt hK hS hW)

theorem tupleChainSharpColumnValuation_of_kerLaws (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup) (h0 : TwTie Tw u μ)
    (Lv : LevTie (tw Tw u μ)) (Vt : ValTie Lv) (Kt : KerTie Lv) (hK : KerLaws Vt Kt)
    (hS : StabUnit (tw Tw u μ)) (hW : WtSigns (tw Tw u μ)) : TupleChainSharpColumnValuation Tw u μ := by

  have hF : FormsStable (tw Tw u μ) := formsStable_of_tgtEq D u _ Lv Kt hK.tgt
  have hUt : UComm (tw Tw u μ) :=
    ⟨fun v φ hφ => hF.1 0 (Nat.zero_le _) v φ hφ, fun v v' _ φ hφ => hF.2.1 0 (Nat.zero_le _) v v' φ hφ⟩
  exact tuple_chain_sharp_column_valuation D u Tw μ Lv Vt Kt hK hS hW
    (step0Tie_of_twTie Tw μ h0 (uComm_own_of_twTie Tw μ h0 hUt))

end GlobalTheory.LvT.TwColumn

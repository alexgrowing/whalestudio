import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFramesStatement

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOrbit

theorem mem_ngSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').ngSet ↔ t.G ≠ 0 ∧ ¬ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ ¬ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem mem_genSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').genSet ↔ t.G ≠ 0 ∧ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem img_inv_img {D : D7} (Z : LocDat D) (p : PlF D) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (A : Submodule (Z.M p).L.O (Vp D p)) : LocNG.img h⁻¹ (LocNG.img h A) = A := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨h x, ⟨x, hx, rfl⟩, by simp⟩

theorem noBB_of_moved {D : D7} (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D)
    (hRel : (FP p).RelG (LocNG.theta (Z.M p))) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hh : h ∈ (FP p).UW0)
    (A B : Submodule (Z.M p).L.O (Vp D p)) (hAB : LocNG.img h A = B)
    (hB : ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = B → ¬ LocNG.BBne (H := locH Z p) τ) :
    ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = A → ¬ LocNG.BBne (H := locH Z p) τ := by
  intro d τ hτ hL hbb
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel
  have hm : LocNG.Datum.Moves h d (act.smul ⟨h, hh⟩ d) := (hmv ⟨h, hh⟩ d _).2 rfl
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel h hh d _ τ hτ hm
  exact hB _ _ h1 (by show LocNG.img h τ.abelian₂ = B; rw [hL, hAB]) (h2.2 hbb)

theorem closed_ng_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → LocClosed F F' Z FP (Y.tO u u').ngSet ∧ LocClosed F F' Z FP (Y.tO u u').genSet ∧ (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ ∀ t ∈ (Y.tO u u').genSet, t.G ≠ 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  have gen := fun t Λ hT => GlobalTheory.T.isGenericTerm_iff_no_localDefect_baseFrames D X Y u u' F F' w hw hG Z FP hB hRel t Λ hT
  have pt := fun t Λ hT => (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t Λ hT).1
  have back : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t'.generic → t.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t Λ hT]
    rw [gen t' Λ' hT'] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h hh _ _ hAB (hg p)
  have fwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t.generic → t'.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t' Λ' hT']
    rw [gen t Λ hT] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h⁻¹ (inv_mem hh) _ _ (by rw [← hAB, img_inv_img]) (hg p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_ngSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fun hg => ht.2 (back t t' Λ Λ' hT hT' hloc hg)⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_genSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fwd t t' Λ Λ' hT hT' hloc ht.2⟩
  · intro t ht
    exact ((mem_ngSet_iff Y u u' t).1 ht).1
  · intro t ht
    exact ((mem_genSet_iff Y u u' t).1 ht).1

end GlobalTheory.LocOrbit

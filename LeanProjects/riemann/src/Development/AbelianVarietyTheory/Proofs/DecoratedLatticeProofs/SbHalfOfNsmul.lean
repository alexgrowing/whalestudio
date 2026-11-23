import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineLatModel

variable {D : D7} {S T : HSp D}

theorem sbHalf_of_nsmul {e : AE D} {Λ Λ' : AddSubgroup (WO S T)} {M₁ M₂ : ℕ} (p₁ : 0 < M₁) (p₂ : 0 < M₂)
    (h1 : ∀ u ∈ Λ', M₁ • u ∈ Λ) (h2 : ∀ u ∈ Λ, M₂ • u ∈ Λ') {Φ : WO S T → ℂ} (h : IsSBHalf e Λ Φ) :
    IsSBHalf e Λ' Φ := by
  obtain ⟨a1, k, hk, a2, a3⟩ := h
  refine ⟨a1, M₁ * M₂ * k, Nat.mul_pos (Nat.mul_pos p₁ p₂) hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have e : (M₁ * M₂ * k) • u = k • (M₂ • (M₁ • u)) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [e]
    exact a2 _ (nsmul_mem (h1 u hu) M₂) (GlobalTheory.SplitLinAt.isHalf_nsmul (GlobalTheory.SplitLinAt.isHalf_nsmul hh M₁) M₂) t
  · have e : (M₁ * M₂ * k) • t = M₁ • (M₂ • (k • t)) := by
      rw [smul_smul, smul_smul]
    rw [e]
    exact nsmul_mem (h2 _ (a3 t ht)) M₁

theorem isModel_ext : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (L S : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∀ (n : Type) [Fintype n] [DecidableEq n] (FL : GlobalTheory.LocMod.Frame k L.rank Unit) (FS : GlobalTheory.LocMod.Frame k S.rank n), (GlobalTheory.LocMod.Place.ofSplitPt p).IsModel ψ FL FS (T₁ ∘ₗ GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS) := by
  classical
  intro D k _ _ _ _ p ψ hψ _ L S ζ hζ LS hS g₁ T₁ hg₁ hT n _ _ FL FS
  have he : IsSplitIdem D p.e := p.split
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    exact hζ.2 (by simp)
  have hlat : Submodule.IsLattice D.host.E
      (Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) := by
    refine ⟨Submodule.fg_span_singleton ζ, ?_⟩
    rw [Submodule.span_span_of_tower]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hζ0, Module.finrank_fin_fun, hζ.1]
  have hA : ∀ u ∈ latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _)
      (fun _ => True), IsHalf p.e u →
      u ∈ latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v) :=
    fun u hu hh => GlobalTheory.SplitLinAt.latHalf D k p L S _ LS u hu (Or.inl hh)
  have hle := GlobalTheory.SplitLinAt.latO_le (S := L) (T := S)
    ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)
  have hT' := (GlobalTheory.SplitLinAt.placeModel_congr hA hle).1 hT
  have dL := GlobalTheory.PlaceModel.isSelfDualC_latFrame L
  have hsb : ∀ Φ, IsSBHalf p.e
      (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v))
      (GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS Φ) := fun Φ => by
    have h0 := GlobalTheory.LocMod.Witness.ext_sb (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS dL hS Φ
    obtain ⟨M₁, p₁, h₁⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := L) (T := S) hlat.fg hS.1.fg dL.1 hS.1
    obtain ⟨M₂, p₂, h₂⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (S := L) (T := S) dL.1.fg hS.1.fg hlat hS.1
    exact (GlobalTheory.SplitLinAt.sbHalf_congr hA hle).2 (sbHalf_of_nsmul p₁ p₂ h₁ h₂ h0)
  refine ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
  · exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hlat hS.1 he.1 he.2.1 (GlobalTheory.PlaceCoord.infPart_split he) hg₁ T₁ hT' _
      ((GlobalTheory.SplitLinAt.sbHalf_congr hA hle).1 (hsb Φ))
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine Eq.trans (congrArg T₁ ?_) (hT.trans _ (hsb Φ) _ (GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS x))
    funext t
    rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.down_add,
      GlobalTheory.LocMod.Witness.down_up, h]
    exact if_congr (GlobalTheory.LocMod.Witness.half_add (GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS x)).symm rfl rfl
  · rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine Eq.trans (congrArg T₁ ?_) (hT.modul _ (hsb Φ) _ hy)
    funext t
    rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, h]
    split_ifs with ht
    · rw [GlobalTheory.LocMod.Witness.up_down (GlobalTheory.LocMod.Place.ofSplitPt p) FL FS ht]
    · rw [mul_zero]

end GlobalTheory.LineLatModel
end

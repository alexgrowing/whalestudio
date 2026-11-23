import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.FrameMove

variable {D : D7}

theorem levChi_datY (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    levChi V β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) κ =
      ((ext1 P.H P.chi (rTup β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (finE V κ)) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  simp [datY]
  rfl

set_option maxHeartbeats 1600000 in

theorem frame_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i n hF PY PW hY hW P
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (Fin.pos i)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg
    hrk hc hc' (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := GlobalTheory.KapIsot.frames_inner (Yc D 0) (Wc D i) hF PY PW hY hW
    (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact GlobalTheory.KapIsot.odd_r D.R) _ _ _ j Φ hΦ
  refine ⟨h, fun κ hκ => ?_⟩
  have hx := hh (h⁻¹ * κ * h)
  rw [show h * (h⁻¹ * κ * h) * h⁻¹ = κ by group] at hx
  obtain ⟨l1, l2⟩ := GlobalTheory.LevTrans.levtrans (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ ⟨PY.ψ (h⁻¹ * κ * h), PY.into _⟩
  rw [hx] at l1 l2
  obtain ⟨hp, hH⟩ := mem_lev.1 hκ.2
  have hpY := l1.2 hp
  have hrt : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ)) =
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h))) := l2 hpY
  refine ⟨?_, ?_⟩
  · show PY.ψ (h⁻¹ * κ * h) ∈
      (GfC (Yc D 0) ⊓ (lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) : Subgroup _)
    refine Subgroup.mem_inf.2 ⟨PY.into _, ?_⟩
    show finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)) ∈ lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)
    refine mem_lev.2 ⟨hpY, ?_⟩
    rw [← hrt]
    exact hH
  · have e1 : levChi (Wc D i) (R.βW i) (R.datWp i P) (PW.ψ κ) =
        ((ext1 P.H P.chi (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ))) : ℂˣ) : ℂ) :=
      levChi_datY (Wc D i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) R.Pg P (fun _ _ => 1) (fun _ => 1) (PW.ψ κ)
    have e2 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) =
        ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)))) : ℂˣ) : ℂ) :=
      levChi_datY (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) R.Pg P R.chi (fun _ => 1) (PY.ψ (h⁻¹ * κ * h))
    rw [e1, e2, hrt]

end GlobalTheory.FrameMove

end

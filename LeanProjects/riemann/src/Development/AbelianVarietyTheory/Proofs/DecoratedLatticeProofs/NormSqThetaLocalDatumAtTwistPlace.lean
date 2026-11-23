import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitWeilPhiInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.ThetaNormTwist

theorem normSq_thetaLocalDatum_at_twistPlace_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) → ∀ r : ℕ, r ≤ S.rank → r ≤ T.rank → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v r mu)) x → nrm2 m X x = zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hcov hfS hfT PP v φ e he hP hA r hrS hrT ξ mu hmu x hx
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  obtain ⟨⟨Tm, hTm⟩, hxall⟩ := hx
  have hxT := hxall Tm hTm
  have hco := (GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he (frCo φ βS) (frCo φ βT)).1
  let ν : Measure (Fv D.host.F v) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hv0, hvT, hiso⟩ := GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ m X hB hcov v e he.1
    T.rank S.rank (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.mapCo φ S T (frCo φ βS) (frCo φ βT)) hco Tm hTm ν hν
  obtain ⟨hip, hSB⟩ := GlobalTheory.T.split_weil_phi_inner_product D PP v φ hP S.rank T.rank r hrS hrT ξ mu hmu ν hν

  obtain ⟨⟨a0, ha0, -, hmax, himg⟩, -⟩ :=
    GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hB.2.2.1 hB.2.2.2.1 hfS hfT v φ e he
  have hval : Valued.v (rdQ φ a0) = 1 := by
    obtain ⟨⟨a1, ha1, h1⟩, hle⟩ := hA
    exact le_antisymm (hle a0 ha0) (h1 ▸ hmax a1 ha1)
  rw [hval] at himg
  have key := hiso _ hSB _ hSB
  rw [himg, hip] at key
  rw [← GlobalTheory.PlaceTensor.onHalf_eq_pull] at key
  rw [← hxT] at key
  have hne : ((GlobalTheory.SplitWeil.volM ν (Fin T.rank) (Fin S.rank) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal : ℂ) ≠ 0 := by
    rw [← himg]
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO m X x x = ((nrm2 m X x : ℝ) : ℂ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO nrm2
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e2] at key
  push_cast at key
  have key2 := mul_left_cancel₀ hne key
  apply Complex.ofReal_injective
  rw [key2]
  push_cast
  ring

end GlobalTheory.ThetaNormTwist

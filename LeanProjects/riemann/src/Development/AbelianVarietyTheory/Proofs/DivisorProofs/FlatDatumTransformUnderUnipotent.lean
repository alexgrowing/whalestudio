import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

noncomputable section

namespace GlobalTheory.SympDatum

theorem datum_actU : ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g) (M : Submodule ℤ (Fl g)), IsLat M → latAct M γ ≤ stdLat g → ∀ (j : Fl g → Pt (symMat g) g → ℂ) (m : Pt (symMat g) g → ℝ), IsDatum (siegel g) tauU (stdLat g) j m → ChernIsFlat (siegel g) tauU m → IsDatum (siegel g) tauU M (fun l P => j (l ᵥ* (γ⁻¹).mat) (actU γ P)) (fun P => m (actU γ P)) ∧ ChernIsFlat (siegel g) tauU (fun P => m (actU γ P)) := by
  intro g γ M hM hMs j m hD hC
  obtain ⟨hτ, -, hF, hMet⟩ := hD
  obtain ⟨hbij, hdiff, hpt⟩ := GlobalTheory.UnivAction.univAct g γ
  have hO : IsOpen (cov (siegel g) g) := hτ.1.prod isOpen_univ
  have hmaps : Set.MapsTo (actU γ) (cov (siegel g) g) (cov (siegel g) g) := hbij.mapsTo
  have hlat : ∀ l ∈ M, l ᵥ* (γ⁻¹).mat ∈ stdLat g := fun l hl =>
    hMs ⟨l, hl, rfl⟩
  have htr : ∀ l : Fl g, ∀ P ∈ cov (siegel g) g,
      actU γ (transl tauU l P) = transl tauU (l ᵥ* (γ⁻¹).mat) (actU γ P) := by
    intro l P hP
    obtain ⟨hY, hta, -, -, -⟩ := hpt P hP
    have e := GlobalTheory.SympFlatChange.per_moeb γ hY l
    refine Prod.ext rfl ?_
    show (P.2 + per (tauU P.1) l) ᵥ* (den γ (tauU P.1))⁻¹ =
      P.2 ᵥ* (den γ (tauU P.1))⁻¹ + per (tauU (actU γ P).1) (l ᵥ* (γ⁻¹).mat)
    rw [hta, e, Matrix.add_vecMul]
  have hAs : ContDiffOn ℝ ∞ (actU γ) (cov (siegel g) g) :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn hO hdiff ∞).restrict_scalars ℝ
  refine ⟨⟨hτ, hM, ⟨fun l hl => ⟨?_, fun P hP => hF.1 _ (hlat l hl) |>.2 _ (hmaps hP)⟩,
      fun l hl l' hl' P hP => ?_⟩, ⟨hMet.1.comp hAs hmaps, fun P hP => hMet.2.1 _ (hmaps hP),
      fun l hl P hP => ?_⟩⟩, fun P hP v w => ?_⟩
  · exact (hF.1 _ (hlat l hl)).1.comp hdiff hmaps
  · show j ((l + l') ᵥ* (γ⁻¹).mat) (actU γ P) =
      j (l ᵥ* (γ⁻¹).mat) (actU γ (transl tauU l' P)) * j (l' ᵥ* (γ⁻¹).mat) (actU γ P)
    rw [Matrix.add_vecMul, htr l' P hP]
    exact hF.2 _ (hlat l hl) _ (hlat l' hl') _ (hmaps hP)
  · show m (actU γ (transl tauU l P)) * ‖j (l ᵥ* (γ⁻¹).mat) (actU γ P)‖ ^ 2 = m (actU γ P)
    rw [htr l P hP]
    exact hMet.2.2 _ (hlat l hl) _ (hmaps hP)
  · have hu : ContDiffOn ℝ 2 (fun Q => Real.log (m Q)) (cov (siegel g) g) :=
      (hMet.1.log fun Q hQ => (hMet.2.1 Q hQ).ne').of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.2 le_top)
    have e := GlobalTheory.ddc_comp_holomorphic _ _ (actU γ) _ hO hO hdiff hmaps hu P hP v w
    rw [e, hC _ (hmaps hP), ← (hpt P hP).2.2.2.1]
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl

end GlobalTheory.SympDatum

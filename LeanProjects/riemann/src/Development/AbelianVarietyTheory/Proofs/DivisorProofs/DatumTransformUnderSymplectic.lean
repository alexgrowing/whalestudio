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

namespace GlobalTheory.ThetaPull

theorem isDatum_pull : ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g) (L : Submodule ℤ (Fl g)), IsLat L → L ≤ stdLat g → ∀ (j : Fl g → Pt (symMat g) g → ℂ) (m : Pt (symMat g) g → ℝ), IsDatum (siegel g) tauU (stdLat g) j m → IsDatum (siegel g) (fun s => moeb γ (tauU s)) L (fun l P => j l (actB γ P.1, P.2)) (fun P => m (actB γ P.1, P.2)) := by
  intro g γ L hL hLs j m hD
  have hU : IsPeriodMap (siegel g) tauU := (GlobalTheory.T.siegel_period_map_simply_connected g).1
  have hO : IsOpen (cov (siegel g) g) := hU.1.prod isOpen_univ
  have hb := GlobalTheory.SympBase.main hU γ
  have hsym : ∀ s ∈ siegel g, tauU (actB γ s) = moeb γ (tauU s) :=
    fun s hs => GlobalTheory.UnivAction.tauU_symPart_of_isSymm (hb.1.2.2 s hs).1
  have hmaps : Set.MapsTo (fun P : Pt (symMat g) g => (actB γ P.1, P.2)) (cov (siegel g) g)
      (cov (siegel g) g) := by
    intro P hP
    refine ⟨?_, Set.mem_univ _⟩
    show IsSiegel (tauU (actB γ P.1))
    rw [hsym P.1 hP.1]
    exact hb.1.2.2 _ hP.1
  have hFd : DifferentiableOn ℂ (fun P : Pt (symMat g) g => (actB γ P.1, P.2))
      (cov (siegel g) g) := by
    have h1 : DifferentiableOn ℂ (fun P : Pt (symMat g) g => fun i j => moeb γ (tauU P.1) i j)
        (cov (siegel g) g) :=
      differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j =>
        (hb.1.2.1 i j).comp differentiableOn_fst fun P hP => hP.1
    have h2 := ((GlobalTheory.UnivAction.symPartL g).differentiable.comp_differentiableOn h1).prodMk
      (differentiable_snd.differentiableOn (s := cov (siegel g) g))
    refine h2.congr fun P _ => ?_
    rfl
  have hFs : ContDiffOn ℝ ∞ (fun P : Pt (symMat g) g => (actB γ P.1, P.2)) (cov (siegel g) g) :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn hO hFd ∞).restrict_scalars ℝ
  have htr : ∀ P ∈ cov (siegel g) g, ∀ l : Fl g,
      ((actB γ (transl (fun s => moeb γ (tauU s)) l P).1,
        (transl (fun s => moeb γ (tauU s)) l P).2) : Pt (symMat g) g) =
        transl tauU l (actB γ P.1, P.2) := by
    intro P hP l
    show ((actB γ P.1, P.2 + per (moeb γ (tauU P.1)) l) : Pt (symMat g) g) =
      (actB γ P.1, P.2 + per (tauU (actB γ P.1)) l)
    rw [hsym P.1 hP.1]
  obtain ⟨-, -, ⟨hjd, hjc⟩, hms, hmp, hmi⟩ := hD
  refine ⟨hb.1, hL, ⟨fun l hl => ⟨(hjd l (hLs hl)).1.comp hFd hmaps,
    fun P hP => (hjd l (hLs hl)).2 _ (hmaps hP)⟩, fun l hl l' hl' P hP => ?_⟩,
    ⟨hms.comp hFs hmaps, fun P hP => hmp _ (hmaps hP), fun l hl P hP => ?_⟩⟩
  · dsimp only
    rw [htr P hP l']
    exact hjc l (hLs hl) l' (hLs hl') _ (hmaps hP)
  · dsimp only
    rw [htr P hP l]
    exact hmi l (hLs hl) _ (hmaps hP)

end GlobalTheory.ThetaPull

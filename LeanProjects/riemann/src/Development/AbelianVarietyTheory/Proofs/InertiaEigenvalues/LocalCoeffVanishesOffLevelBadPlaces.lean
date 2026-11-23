import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfLevelDatumNeZeroTranslateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuppFLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.BadSuppPf

theorem rank_le (D : D7) (i : Fin D.R.m) : (Wc D i).rank ≤ (Vc D i).rank := by
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  exact r_le_V i

theorem badSupp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ P hP e f hPf k hk hnot
  classical
  have hv := hL.thP.vP i t
  have hθ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  obtain ⟨-, e', he', hth⟩ := hv
  obtain ⟨cV, hBV⟩ := hL.lev.βV i
  obtain ⟨cW, hBW⟩ := hL.lev.βW i
  rw [one_pow] at hBV hBW
  have hsdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i)
  have hsdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i)
  have hdat : (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e') x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
          omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) = GlobalTheory.FinZeta.levDatum (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t) (R.xiR t) e' := by
    funext x
    simp only [GlobalTheory.FinZeta.levDatum, GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv R i]
  rw [hdat] at hth
  obtain ⟨hkf, hk1⟩ := GlobalTheory.SuppLocal.suppF_local D (Wc D i) P e f k hPf hk
  have hZ : ∀ PP, PP ∈ R.Pg ∪ R.Q t ↔ PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ R.Q t := fun PP => Finset.mem_union
  have hsb := GlobalTheory.FinZeta.isSBHalf_levDatum D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv)
    (R.Q t) (R.xiR t) (R.Pg ∪ R.Q t) e' hsdV hsdW hBV.1 hBW.1 he'
  have horth := GlobalTheory.ThetaOrth.orth D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hF i t).datum (R.ΛV i) (R.ΛW i) hsdV hsdW
    (R.Pg ∪ R.Q t) e' he' (R.vacP i) _ (R.vP i t) hsb hth hθ μ 𝓕 hμ k hkf (fun x hx => by
      by_contra hx'
      obtain ⟨k', hk', hag⟩ := GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate D (Vc D i) (Wc D i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
        (R.xiR t) (R.Pg ∪ R.Q t) e' hsdW hBW.1 (rank_le D i) rfl he' hZ k hkf x hx hx'
      apply hnot
      have hlo := (GlobalTheory.FinZeta.LevelOff.level_offS D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i R.triv) ((R.Pg ∪ R.Q t).image (fun PP => PP.under (𝓞 D.host.F))) hBW
        (fun PP hPP => Finset.mem_image_of_mem _ (by
          rcases hPP with h | h
          · exact Finset.mem_union_left _ h
          · exact absurd h (Finset.notMem_empty _)))).2.1 k hkf
      refine hlo.2 ⟨⟨k', hk', fun v hvS => ?_⟩, fun v hvS => ?_⟩
      · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hvS
        exact hag PP hPP
      · have hne : v ≠ P.under (𝓞 D.host.F) := fun h => hvS (h ▸ Finset.mem_image_of_mem _
          (hP.elim (fun h => Finset.mem_union_left _ h) (fun h => Finset.mem_union_right _ h)))
        rw [hk1 v hne]
        exact Subgroup.one_mem _)
  have h0 : thetaIP μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := by
    have h1 : Formalism.IndefR.Lift.pet μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := horth
    unfold Formalism.IndefR.Lift.pet at h1
    unfold thetaIP
    have h2 : (fun w => star (R.ωP i t (1, k) (R.vP i t) w) * R.vP i t w) =
        fun w => starRingEnd ℂ (R.ωP i t (1, k) (R.vP i t) w * starRingEnd ℂ (R.vP i t w)) := by
      funext w; simp [mul_comm]
    rw [h2, integral_conj, h1, map_zero]
  unfold coef
  rw [h0, zero_div]

end GlobalTheory.BadSuppPf

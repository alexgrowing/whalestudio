import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalfStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProdStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDualStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twVec' : TwVec' := by
  intro B X I hOk hPins l Z u a Ch A hA ψ θ x vac c₀ hX k _ _ _ _ ι p β Q hStd J hPl j hj α γ cT hReps e he
  have hjm : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hL0 : ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs j hjm).2.2
  have hL1 : ∀ z, z ∈ (x (j + 1)).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs (j + 1) hj).2.2
  have hvac := hX.vc j (by omega)
  have hS0 : ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL0 z
  have hS1 : ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL1 z
  have hV : Vac ψ _ _ (x j).L (x (j + 1)).L (fun v => ∃ i, v = (p i).v) (vac j) := by
    refine ⟨hvac.2.theta, ?_⟩
    have hle : latO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) (fun v => ∃ i, v = (p i).v) ≤ stdHom _ _ := by
      rw [hS0, hS1]
      apply AddSubgroup.closure_mono
      rintro w ⟨a, ha, -, rest⟩
      exact ⟨a, ha, fun _ h => absurd trivial h, rest⟩
    exact ⟨fun u hu => hvac.2.lat.1 u (hle hu), fun e' he' u hu hh => hvac.2.lat.2 e' he' u (hle hu) hh⟩
  have hO := hReps.2 (vac j) hV
  obtain ⟨eq, heq⟩ := hStd.1
  have hF := GlobalTheory.T.putInSplitPlaces_datum_product_on_half (I.rec7 l Z) k ι p J hPl _ _ ψ hX.std _ _ (β j) (β (j + 1)) (x j).L (x (j + 1)).L
    (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z j hjm _ hL0) (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z (j + 1) hj _ hL1) hL0 hL1 _ e he ⟨eq, heq⟩ _ (vac j) _ hvac.2.theta hvac.2.lat hO
  have hval := GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod I hOk hPins l Z u a Ch A hA k ι p β Q _ hStd J hPl j hj α γ
  convert hF using 2 with z
  exact hval z

end GlobalTheory.AdForm

end

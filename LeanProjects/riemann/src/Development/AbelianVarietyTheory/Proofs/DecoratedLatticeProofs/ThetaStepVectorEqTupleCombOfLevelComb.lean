import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalvesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodingeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfProd

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm GlobalTheory.ExportSeries

variable {D : D7}

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stepVec_of_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ : WO S T → ℂ) (dG dQ : WO S T →₀ ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q → (∀ PP ∈ Pg, ∀ PP' ∈ Q, PP.under (𝓞 D.host.F) ≠ PP'.under (𝓞 D.host.F)) → (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Pg, p = PP.under (𝓞 D.host.F)) dG → GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ Q, p = PP.under (𝓞 D.host.F)) dQ → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj ∅ (fun _ => 1) f₀ (comb ψ S T dG f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ f₀) → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj Q ξ f₀ (comb ψ S T dQ (comb ψ S T dG f₀)) := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT r t j hr Pg Q P χ χj ξ f₀ dG dQ hS hT _ _ hdisj hunder hex hdG hdQ hG hQv
  obtain ⟨hvac, eG, heG, hthG⟩ := hG
  obtain ⟨-, eQ, heQ, hthQ⟩ := hQv
  obtain ⟨e, he⟩ := hex
  change IsIdemSum eG (Pg ∪ ∅) at heG
  change IsIdemSum eQ (∅ ∪ Q) at heQ
  rw [Finset.union_empty] at heG
  rw [Finset.empty_union] at heQ
  have heq : e = eG + eQ := by
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := heQ
    have := GlobalTheory.IdemSumAdd.idemSum_union D eG e Pg Q es hdisj hes heG he
    rw [this, hsum]
  subst heq
  refine ⟨hvac, eG + eQ, he, ?_⟩
  have hGG := idemSum_mul_self heG
  have hQQ := idemSum_mul_self heQ
  have hee := idemSum_mul_self he
  have hGQ : eG * eQ = 0 := by
    have h2 : (2 : AE D) * (eG * eQ) = 0 := by
      have h := hee
      rw [add_mul, mul_add, mul_add, hGG, hQQ, mul_comm eQ eG] at h
      linear_combination h
    have h2' : (2 : AE D) = algebraMap D.host.F (AE D) 2 := (map_ofNat _ 2).symm
    calc eG * eQ = algebraMap D.host.F (AE D) (1 / 2) * ((2 : AE D) * (eG * eQ)) := by
          rw [← mul_assoc, h2', ← map_mul, show (1 / 2 : D.host.F) * 2 = 1 by norm_num, map_one, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      a • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun a ha u hu =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO hS.1 hT.1 βS βT
  have hsbG := isSBHalf_of_red eG _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (infPart_of_half (infPart_idemSum heG) ht)⟩ Pg
    (fun y => omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj y *
      omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 y) fun y y' h => by
      rw [omegaG_congr _ χj y y' h, omegaQ_congr ∅ _ _ 1 y y' fun PP hP => absurd hP (Finset.notMem_empty PP)]
  have hsbQ := isSBHalf_of_red eQ _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (infPart_of_half (infPart_idemSum heQ) ht)⟩ Q
    (fun y => omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj y *
      omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 y) fun y y' h => by
      rw [omegaG_congr _ χj y y' fun PP hP => absurd hP (Finset.notMem_empty PP), omegaQ_congr Q _ _ 1 y y' h]
  refine ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hvac.1 S T ΛS ΛT hS hT (Pg ∪ Q) (eG + eQ) he f₀
    hvac.2.theta hvac.2.lat).1, fun Tm hTm => ?_⟩
  have hTG := isPlaceModel_comp_restrictHalf hGG hQQ hGQ hΛ hTm
  have hTm' := hTm
  rw [add_comm eG eQ] at hTm'
  have hTQ := isPlaceModel_comp_restrictHalf hQQ hGG (by rw [mul_comm, hGQ]) hΛ hTm'
  have hvG := hthG.2 _ hTG
  have hvQ := hthQ.2 _ hTQ
  have hL1 := isPlaceModel_prodHalf hGG hQQ hGQ hΛ hsbQ hTm
  have hbase : ∀ Ψ : WO S T → ℂ, prodHalf eG eQ Ψ (halfInd eG (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) = restrictHalf eQ eG (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Ψ := fun Ψ => by
    funext x
    simp only [prodHalf_apply, restrictHalf_apply, add_comm eG eQ]
    ring
  rw [hbase, ← LinearMap.comp_apply, ← hvQ] at hL1
  have hd : ∀ PP ∈ Pg, ¬ (fun p => ∃ PP ∈ Q, p = PP.under (𝓞 D.host.F)) (PP.under (𝓞 D.host.F)) :=
    fun PP hP ⟨PP', hP', h⟩ => hunder PP hP PP' hP' h
  have hL2 := GlobalTheory.T.supportedTranslatesCombination_commutes_schrodinger D ψ hvac.1 S T _ eG Pg _ heG hd dQ hdQ f₀ _ (combL ψ S T dQ ∘ₗ
    (Tm ∘ₗ restrictHalf eG eQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)))
    hTG fun Φ => by rw [LinearMap.comp_apply, combL_apply]
  have hu := placeModel_eq hvac.1 hS hT hGG (infPart_idemSum heG) hL1 hL2 hsbG
  rw [LinearMap.comp_apply, LinearMap.comp_apply, combL_apply, ← hvG] at hu
  rw [← hu]
  beta_reduce
  congr 1
  funext x
  exact (GlobalTheory.T.stepDatum_eq_mul_halves D S T βS βT r t j hr Pg Q P χ χj ξ eG eQ heG heQ hGQ x).symm

end GlobalTheory.HalfProd

end

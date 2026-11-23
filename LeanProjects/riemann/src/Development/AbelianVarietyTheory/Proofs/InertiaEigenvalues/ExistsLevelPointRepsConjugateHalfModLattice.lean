import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsModHalfLatticeFinsetSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsHalfSplitPlaceNormPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormMaxPowDividingConjugatePlaceStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.FlipReps

theorem flip_reps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ Y.card = flipIdx V W T m := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  obtain ⟨-, -, -, -, hSV, hSW, -⟩ := hP
  have hm0 : 0 < m := hm.pos
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  set Λ := latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) with hΛ
  have hcard : Nat.card (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m) = flipIdx V W T m := by
    have hc' : cA D eT = ∑ PP ∈ T, cA D (es PP) := by rw [hsum, map_sum]
    rw [hc', GlobalTheory.T.card_divisionPointsModHalfLattice_finset_sum Λ (fun c hc u hu => GlobalTheory.PlaceModelSum.idem_smul_latO hc hu) T (fun PP => cA D (es PP)) ?_ ?_ m]
    · unfold flipIdx
      refine Finset.prod_congr rfl fun PP hPP => ?_
      have hi : Formalism.L2.NTheta.IsIdemAt (cA D (es PP)) (Formalism.L2.DIV.conjPl PP) :=
        GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun _ => Iff.rfl
      rw [GlobalTheory.T.card_divisionPoints_half_split_place_norm_pow D V W ΛV ΛW hSV hSW _ _ hi m hm0, GlobalTheory.T.absNorm_maxPowDividing_conjugatePlace]
    · intro i hi; rw [← map_mul, (hes i hi).1.1]
    · intro i hi j hj hij; rw [← map_mul, GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij, map_zero]
  have hfin : Finite (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact flipIdx_ne_zero V W T hm0.ne')
  letI := Fintype.ofFinite (GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m)
  have hhalf : ∀ y : WO V W, cA D eT • y = y → IsHalf (cA D eT) y := fun y hy =>
    (GlobalTheory.PlaceModel.isHalf_iff V W).2 ((GlobalTheory.PlaceModel.mem_half V W).2 hy)
  have hhalf' : ∀ y : WO V W, IsHalf (cA D eT) y → cA D eT • y = y := fun y hy =>
    (GlobalTheory.PlaceModel.mem_half V W).1 ((GlobalTheory.PlaceModel.isHalf_iff V W).1 hy)
  refine ⟨Finset.univ.image (fun q : GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m =>
    ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W)), ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hhalf _ (GlobalTheory.DivPtFourier.rep q).2.1, (GlobalTheory.DivPtFourier.rep q).2.2⟩
  · intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have hqq : q' = q := by
      rw [← GlobalTheory.DivPtFourier.mk_rep q, ← GlobalTheory.DivPtFourier.mk_rep q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨?_, ?_⟩
      · have : ((-GlobalTheory.DivPtFourier.rep q' + GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) =
            ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) -
              ((GlobalTheory.DivPtFourier.rep q' : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) := by
          push_cast; abel
        rw [this]; exact hyy
      · exact (GlobalTheory.PlaceModel.half V W (cA D eT)).add_mem ((GlobalTheory.PlaceModel.half V W (cA D eT)).neg_mem
          ((GlobalTheory.PlaceModel.mem_half V W).2 (GlobalTheory.DivPtFourier.rep q').2.1))
          ((GlobalTheory.PlaceModel.mem_half V W).2 (GlobalTheory.DivPtFourier.rep q).2.1)
    rw [hqq]
  · intro y hy hmy
    have hyd : y ∈ GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m := ⟨hhalf' y hy, hmy⟩
    set q : GlobalTheory.DivPtFourier.DQ Λ (cA D eT) m := QuotientAddGroup.mk (⟨y, hyd⟩ : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m))
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩
    have h := GlobalTheory.DivPtFourier.mk_rep q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : ((-GlobalTheory.DivPtFourier.rep q + ⟨y, hyd⟩ : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) =
        y - ((GlobalTheory.DivPtFourier.rep q : ↥(GlobalTheory.DivPtFourier.divPts Λ (cA D eT) m)) : WO V W) := by
      push_cast; abel
    rw [← this]; exact h.1
  · rw [Finset.card_image_of_injective _ GlobalTheory.DivPtFourier.rep_injective, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]

end GlobalTheory.FlipReps
end

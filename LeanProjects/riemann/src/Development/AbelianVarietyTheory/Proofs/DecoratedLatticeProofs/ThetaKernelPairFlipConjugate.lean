import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.KernelFlip

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem annih_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T)
    {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT)
    (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ T S) θ τ (cplxO bT aS) w (dag S T f) =
      dag S T (annih (heisO ψ S T) θ τ (cplxO aS bT) (GlobalTheory.FockAdjoint.cdag S T τ w) f) := by
  unfold annih
  rw [GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.cdag_cplx τ hS hT,
    GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hf]
  funext x
  simp only [dag, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, map_add, map_mul, map_neg, Complex.conj_I]
  ring

theorem annih_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf))

theorem foldr_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : RealMat S) (sT : RealMat T)
    (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => exact hg
  | cons p l ih => exact annih_theta hψ hθ _ _ _ ih

theorem foldr_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (l : List (D.what₂.Tau × Matrix (Fin S.rank) (Fin T.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    l.foldr (fun p f => annih (heisO ψ T S) θ p.1 (cplxO (sT p.1) (sS p.1)) p.2 f) (dag S T g) =
      dag S T ((l.map fun p => (p.1, GlobalTheory.FockAdjoint.cdag S T p.1 p.2)).foldr
        (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih, annih_dag hψ hθ L p.1 (hS p.1) (hT p.1) _ (foldr_theta hψ hθ sS sT _ hg)]

theorem fock_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) {Φ : WO S T → ℂ}
    (h : IsFockVec ψ θ S T sS sT Φ) : IsFockVec ψ θ T S sT sS (dag S T Φ) := by
  obtain ⟨hth, N, hN⟩ := h
  refine ⟨L.theta Φ hth, N, fun l hl => ?_⟩
  rw [foldr_dag hψ hθ L sS sT hS hT l hth, hN _ (by simpa using hl)]
  funext x
  simp [dag]

theorem coef_dag (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) {X : Type} (x : X → WO T S → ℂ) (x' : X → WO S T → ℂ)
    (hx : ∀ p, x' p = dag T S (x p)) (Φ : WO T S → ℂ) (c : X → ℂ) (h : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef T S x Φ c) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef S T x' (dag T S Φ) fun p => starRingEnd ℂ (c p) := by
  obtain ⟨μ, 𝓕, ⟨hμ, h𝓕, h1⟩, hc⟩ := h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have : BorelSpace (WO T S) := ⟨rfl⟩
  have : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, ⟨hHaar, hF, ?_⟩, fun p => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · show starRingEnd ℂ (c p) = _
    rw [hc p, MeasurableEquiv.restrict_map, hpre, integral_map_equiv, ← integral_conj, hx p]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have ew : eM.symm (eM w) = w := eM.symm_apply_apply w
    show starRingEnd ℂ (x p w * starRingEnd ℂ (Φ w)) =
      dag T S (x p) (eM w) * starRingEnd ℂ (dag T S Φ (eM w))
    simp only [dag]
    have e2 : adjO T S (eM w) = w := hTS.invol w
    rw [e2, map_mul]

end GlobalTheory.KernelFlip

open GlobalTheory.KernelFlip in

theorem GlobalTheory.KernelFlip.kernelPair_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB true (fun _ => True) (fun _ => True) K₁ K₂ c → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c := by
  intro D ψ θ A B χA χB sA sB K₁ K₂ c hθ hsA hsB hK
  obtain ⟨om, Φ₁, Φ₂, H, hF₁, hF₂, -, -, hK₁, hK₂, hc⟩ := hK
  have hψ : IsStdChar D ψ (-1) := H.std
  have hBA : AdjLaw ψ B A := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ B A
  have hAB : AdjLaw ψ A B := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ A B
  obtain ⟨om', H', hom'⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ B A χB χA om H
  have hθK : ∀ (g : GA D A) (h : GA D B) (Φ : WO B A → ℂ),
      starRingEnd ℂ (thetaKO om' g h (dag B A Φ)) = thetaKO om h g Φ := by
    intro g h Φ
    simp only [thetaKO]
    rw [hom' h g Φ]
    simp only [dag]
    rw [GlobalTheory.WeilConj.adjO_zero hBA, Complex.conj_conj]
  refine ⟨om', dag B A Φ₁, dag B A Φ₂, H', fock_dag hψ hθ hBA sB sA hsB hsA hF₁,
    fock_dag hψ hθ hBA sB sA hsB hsA hF₂, trivial, trivial, fun g h => ?_, fun g h => ?_, ?_⟩
  · rw [hθK, hK₁]
  · rw [hθK, hK₂]
  · exact coef_dag hAB hBA (fun g : GA D A => om (1, g) Φ₁) (fun g : GA D A => om' (g, 1) (dag B A Φ₁))
      (fun g => hom' 1 g Φ₁) Φ₂ c hc

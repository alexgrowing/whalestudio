import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem mem_bottomPairFinitePlacesBelow_of_mem_exceptional {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {v : FinPl D} (hv : v ∈ G.pl.S0) : v ∈ sfB G t := by
  classical
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl GlobalTheory.ChiGrid.Places.W0
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨_, hw, G.pl.under_w hv⟩

theorem under_mem_sfB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ locPl G t) : w.under (𝓞 D.host.F) ∈ sfB G t := by
  classical
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨w, hw, rfl⟩

theorem unrOff_betaB_div_alphaB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) :
    GlobalTheory.LFun.UnrOff (betaB G i j / alphaB Lc i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) := by
  classical
  intro w hw
  have hw' : w.under (𝓞 D.host.F) ∉ sfB G t := hw
  have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
  have hQ : ∀ P ∈ Lc.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
    hw' (e ▸ under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hv)
  have hμ0 : GlobalTheory.LFun.UnrAt (Lc.mu0 ((j : ℕ) + 1)) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 ((Lc.C.isMu0 j).unr w fun k hk => hv ?_)
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  have hξ : GlobalTheory.LFun.UnrAt (Lc.xi t) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hn
    rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ w hq rfl
    · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
  have e : betaB G i j / alphaB Lc i j t = G.ch.chi (D.R.m - i) * (Lc.mu0 ((j : ℕ) + 1) * Lc.xi t)⁻¹ := by
    unfold betaB alphaB
    rw [mul_div_mul_right_eq_div, div_eq_mul_inv]
    rfl
  rw [e]
  exact hχ.mul (hμ0.mul hξ).inv

theorem isSphOff_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (sS : RealMat S) (sT : RealMat T)
    (BS : RealMat S) (BT : RealMat T) (LS : Lat S) (LT : Lat T) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Pset)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (FinPl D)) (hP : ∀ PP ∈ Pset, PP.under (𝓞 D.host.F) ∈ Sf)
    (hpt : ∀ φ, IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  GlobalTheory.FockSph.isLatVac_pureTensorO_off hvac.2.inf BS BT hvac he hth Sf hP (fun φ => (hpt φ).1) φ

theorem unram_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, Unram W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) X.rA.Λ X.rW.Λ (GlobalTheory.BottomIPData.sfB G t) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  have hpt := GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hψ hθ cS cT X.rA.B X.rW.B hf hv
  have hs := isSphOff_pureTensorO (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.rA.Λ X.rW.Λ
    h.isVac (h.idem t) (h.fst t) (sfB G t) (fun PP hPP => under_mem_sfB G t hPP) hpt P
  exact ⟨GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1, h.rigW.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2,
    unrOff_betaB_div_alphaB G hL i j t, hs, hs⟩

end GlobalTheory.BottomIPData

end

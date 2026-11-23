import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoChartLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.LevLaw

theorem latFr_stdLat (D : D7) (S : HSp D) (a : ℕ) (hS : S.rank = a) :
    latFr S hS (Formalism.L2.Col.stdLat D.host.E a) = intVec D S.rank := by
  subst hS
  rw [GlobalTheory.LatPairMove.latFr_rfl, coe_colStdLat]

theorem mem_stdHom_iff_actO (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (k : GA D S) (k' : GA D T)
    (h1 : Moves S hS 1 (Formalism.L2.Col.stdLat D.host.E a)) (h1' : Moves T hT 1 (Formalism.L2.Col.stdLat D.host.E b))
    (hk : Moves S hS k (Formalism.L2.Col.stdLat D.host.E a)) (hk' : Moves T hT k' (Formalism.L2.Col.stdLat D.host.E b)) :
    ∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T := by
  have key := GlobalTheory.LatPairMove.latO_move D S T a b hS hT 1 k 1 k' _ _ _ _ h1 h1' (by rwa [mul_one]) (by rwa [mul_one])
  rw [latFr_stdLat, latFr_stdLat] at key
  intro x
  constructor
  · intro hx
    exact (key _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨u₀, hu₀, he⟩ := (key _).1 hx
    have hinv : ∀ v, actO S T k⁻¹ k'⁻¹ (actO S T k k' v) = v := fun v => by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k⁻¹ k'⁻¹ v
      rwa [inv_inv, inv_inv] at this
    have := congrArg (actO S T k⁻¹ k'⁻¹) he
    rw [hinv, hinv] at this
    rw [this]
    exact hu₀

theorem lev_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC j hj α γ κ κ'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  have hSP := hstd.1 j hj1
  obtain ⟨xr, hxr⟩ := hstd.2.2.2.2 _ κ.1
  obtain ⟨yr, hyr⟩ := hstd.2.2.2.2 _ κ'.1
  have hU := hC.is.U j (Nat.le_of_succ_le hj1) (ι j α)
  have hU' := hC.is.U (j + 1) hj1 (ι (j + 1) γ)
  have hkG : κ.1 ∈ GfC _ := ((hU κ.1).1 κ.2).1
  have hkG' : κ'.1 ∈ GfC _ := ((hU' κ'.1).1 κ'.2).1
  have h1G : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) ∈ GfC _ := ((hU 1).1 (one_mem _)).1
  have h1G' : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1))) ∈ GfC _ := ((hU' 1).1 (one_mem _)).1
  have hMk := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) κ.1 κ.2
  have hMk' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) κ'.1 κ'.2
  have hM1 := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) 1 (one_mem _)
  have hM1' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) 1 (one_mem _)
  have hom := hC.om j hj
  have hVT := (hX.mv j hj1).2 a (A.chr (j + 1)) (kom j) (hC.is.chr ⟨j, hj⟩) hom
  have e1 := hVT κ.1 hkG κ'.1 hkG' _ _ hMk hMk' xr yr hxr hyr
  have e0 := hVT 1 h1G 1 h1G' _ _ hM1 hM1' 1 1 (GlobalTheory.SmallFix.isDetRoot_one _) (GlobalTheory.SmallFix.isDetRoot_one _)
  have h11 : kom j ((1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)))) = 1 :=
    map_one (kom j)
  set p : ℂ := ((A.chr (j + 1) xr : ℂ))⁻¹ * (A.chr (j + 1) yr : ℂ) with hpdef
  have hvth : IsThetaFunO ψ _ _ (vac j) := (hX.vc j hj).2.theta
  have hp : kom j (κ.1, κ'.1) (vac j) = p • vac j := by
    have hf : IsThetaFunO ψ _ _ (kom j (κ.1, κ'.1) (vac j) - p • vac j) :=
      GlobalTheory.AvgKill.theta_sub' (hom.om_pres _ _ hvth) (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul p hvth)
    have hz : xiN θ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1) I.A.δ I.A.sc
        (kom j (κ.1, κ'.1) (vac j) - p • vac j) = 0 := by
      funext z
      have a1 := congrFun e1 z
      have a0 := congrFun e0 z
      rw [h11] at a0
      simp only [ColDat.xiS, xiN, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, map_one, Circle.coe_one, inv_one, mul_one] at a1 a0 ⊢
      rw [hpdef, mul_sub, show ∀ q r s : ℂ, q * (r * s) = r * (q * s) from fun q r s => by ring]
      erw [a1, a0]
      ring
    exact sub_eq_zero.1 ((GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective _ ψ θ _ _ _ _ _ _ _ _ hSP).2 _ hf hz)
  obtain ⟨-, Φ, hΦ, hΞ, hth⟩ := hC.dat j hj1 α γ
  have hq : ∀ z, IsHalf A.e z → p * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) =
      (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) * Φ z := fun z hz =>
    GlobalTheory.T.finite_datum_law_under_two_chart_levels I hI hP l Z u a Ch₀ A hC.is j hj1 (ι j α) (ι (j + 1) γ) Φ hΦ (w j α γ) (fun z => hΞ z) κ κ' xr yr hxr hyr z hz
  have hlat := mem_stdHom_iff_actO (I.rec7 l Z) _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1))
    (rankN (I.rec7 l Z) (j + 1) hj1) κ.1 κ'.1 hM1 hM1' hMk hMk'
  exact GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1)
    I.A.δ I.A.sc hSP (A.chr (j + 1)) (kom j) hom A.e _ hC.is.idem (vac j) Φ _ (hX.vc j hj) hΦ hth κ.1 hkG κ'.1 hkG' hlat p _ hp hq

end GlobalTheory.AdForm.LevLaw

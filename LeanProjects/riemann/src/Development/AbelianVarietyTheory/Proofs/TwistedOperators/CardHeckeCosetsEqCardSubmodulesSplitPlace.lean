import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfDepthValuations
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinomStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeCosetCount

theorem card_eq_latCount : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
      Rc.card = Nat.card (GlobalTheory.HeckeCount.LatCount (T.Q.Dw ((i : ℕ) + 1)) p (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal)
        (Ideal.absNorm P.asIdeal ^ k)) := by
  intro D hHP hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hL hG hF hM hTh hTie i σ hσ hV hFP P p k α Rc hs
  obtain ⟨hso, hp, hpP, -, hk, hα, hdc⟩ := hs
  rw [GlobalTheory.T.splitPlace_hecke_doubleCoset_card_gaussBinom D R hL hF i P k α Rc hso hk hα hdc]
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr := (hTie.laws.unf _ hj T.σ₀ T.good_σ₀).1
  have hrk : Module.finrank (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La = D.R.r := by
    rw [(T.Q.Dw ((i : ℕ) + 1)).rank]; omega
  set J := GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal T.Q.H P.asIdeal with hJdef
  have hJm : J.IsMaximal := by
    rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal]
    haveI : P.asIdeal.IsMaximal := P.isMaximal
    exact Ideal.map_isMaximal_of_equiv T.Q.H.bar
  have hpJ : ((p : ℕ) : 𝓞 D.host.E) ∈ J := by
    rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal]
    have := Ideal.mem_map_of_mem (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hpP
    rwa [map_natCast] at this
  have hN : Ideal.absNorm J = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv P.asIdeal J T.Q.H.bar (by rw [hJdef, GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels.conjIdeal])).toEquiv.symm
  rw [← hN, GlobalTheory.T.card_stableLatticeSubgroups_eq_gaussianBinomial _ p J hp.pos hJm hpJ k, hrk]

end GlobalTheory.HeckeCosetCount

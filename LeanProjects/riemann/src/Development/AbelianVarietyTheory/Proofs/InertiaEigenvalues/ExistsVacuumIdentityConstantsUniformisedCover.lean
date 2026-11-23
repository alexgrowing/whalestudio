import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFirst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
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

namespace GlobalTheory.CoverCc

theorem exists_ccIs_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∃ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmods hthP hT i hstd hV C hC
  have hC5 : GlobalTheory.Core5 R F := ⟨hlev, hgrp, hfam, hmods, hthP⟩
  have hσ0 : GoodEmb T.Q.c T.σ₀ := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F hC5 i A.μ0 hstd
  have hM := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ hC5 hT i T.σ₀ rfl
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) T.σ₀ := by
    rw [chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC5.lev.xi_base ▸ hC5.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) T.σ₀ = W),
      MuVal W (T.chiW ((i : ℕ) + 1) T.σ₀) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ0
    exact ⟨hT.laws.muVal _ (inR i) _ hσ0, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (T.dict ((i : ℕ) + 1) T.σ₀ 1).1
  obtain ⟨hD, hFT, -, hσ₂⟩ := GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible D G Pl0 T0 A T R F κ v₀ hL hlev hgrp hfam hmods hthP hT i hstd hV C hC
  exact GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair GlobalTheory.chartIndependence_unconditional hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt
    C.U₂ hσ₂ hC.2.2.2.1 hr1 hC.2.1 hdom hV0 h1 h2 h3 h4 h5 _ _ hD.2.2.1 (fun k τ => hD.2.2.2.1 k τ.1 τ.2)
    (fun k => (hFT k).1) (hC5.thP.vP i A.μ0).1 _

end GlobalTheory.CoverCc

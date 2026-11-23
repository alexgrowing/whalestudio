import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVacuumIdentityConstantsUniformisedCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverInvPhaseConstantsNormalisedDominStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverConstantsUniqueOnDictionaryComponentsStatement
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

namespace GlobalTheory.LevelSeries

theorem covCc_of_pinned : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → CovCc T R i hV ph C := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVs hV ph hph hB C hU hpin
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.exists_vacuumIdentityConstants_uniformisedCover D G Pl0 T0 A T R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVs hV C hU
  have hp2 := GlobalTheory.T.uniformisedCover_invPhase_constants_normalised_dominant D G Pl0 T0 A T R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVs hV ph hph hB C hU cc hcc
  have heq := GlobalTheory.T.coverConstants_unique_on_dictionaryComponents D G Pl0 T0 A T R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVs hV C hU _ hpin hp2
  have hph0 : ph ≠ 0 := by rintro rfl; simp at hph
  refine ⟨fun k => ?_, fun h γ hat hx' g bas idx e hs hi ϑ hϑ w hw0 => ?_⟩
  · rw [norm_mul, hph, (hpin _ (dom_wtA (κ i))).1 k, one_mul]
  · have h1 := hcc.2 h γ hat hx' g bas idx e hs hi ϑ hϑ w hw0
    have key : ph * C.cc₂ (castDict hV C.dict₂ h).1 = cc (castDict hV C.dict₂ h).1 := by
      rw [show castDict hV C.dict₂ h = C.dict₂ (cast (congrArg (GA D) hV.symm) h) from rfl, heq, ← mul_assoc,
        mul_inv_cancel₀ hph0, one_mul]
    beta_reduce
    rw [key]
    exact h1

end GlobalTheory.LevelSeries

import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
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
namespace GlobalTheory.VacTransOrth

theorem vacuumTranslates_conjHalf_sq_norm_eq_card_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y hY hYd μ 𝓕 hμ
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hψ, hf⟩ := hP
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hSV hSW
  have hc0 : infPart D (cA D eT) = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hT
  have hfin : ∀ y ∈ Y, y.map (infPart D) = 0 := fun y hy => by
    ext i j
    show infPart D (y i j) = 0
    rw [← hY y hy i j, RingHom.map_mul, hc0, zero_mul]
  have h := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ V W hψ.1 μ 𝓕 hμ f₀ hf.theta (hf.norm.2 (μ, 𝓕) hμ) (WO V W) Y id
    (fun _ => 1) (fun _ _ => norm_one) ?_
  · simpa only [one_smul, id] using h
  intro y hy y' hy' hne
  have hnot : y - y' ∉ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) :=
    fun hm => hne (hYd y hy y' hy' hm)
  have hm0 : (y - y').map (infPart D) = 0 := by
    ext i j
    have h1 : infPart D (y i j) = 0 := congrFun (congrFun (hfin y hy) i) j
    have h2 : infPart D (y' i j) = 0 := congrFun (congrFun (hfin y' hy') i) j
    show infPart D (y i j - y' i j) = 0
    rw [RingHom.map_sub, h1, h2, sub_zero]
  rw [hd _ hm0] at hnot
  push_neg at hnot
  obtain ⟨l, hl, hne'⟩ := hnot
  obtain ⟨ε, hε, hεf⟩ := hsign f₀ hf.lat l hl
  exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f₀ hf.lat, hne'⟩

end GlobalTheory.VacTransOrth

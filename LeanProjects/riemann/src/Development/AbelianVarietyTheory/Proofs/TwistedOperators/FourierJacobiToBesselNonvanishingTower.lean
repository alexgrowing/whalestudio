import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridConjugationWeilDataInverseCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLiftStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscRungB

theorem rapidDec_star {D : D7} {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  first
  | exact h.conj
  | exact RapidDec.of_le h (fun γ hγ g => by simp only [Pi.star_apply]; rw [h.left hγ g])
      h.continuous.star (fun g => by simp only [Pi.star_apply, norm_star, le_refl])

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.χV = χV ∧ s.χW = χW ∧ s.om = om ∧ s.vW = vW := by
  have hDesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om₁, h₁⟩ := (hDesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hDesc ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩, rfl, rfl, rfl, rfl⟩

theorem rungB : FockTot → PartFixed → RungB := by
  intro hF hP
  unfold RungB OnTower
  intro D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h hJ

  have hi : 2 * k + 1 < D.R.m := by omega
  obtain ⟨hw1, hw2, hodd, -, hdepiff, hdn, hpart, hpartEq, hhaar, hfund⟩ :=
    GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 1) hi
  obtain ⟨hχS, hχT⟩ := hodd (odd_two_mul_add_one k)
  obtain ⟨hrap, hchain⟩ := hΨ
  obtain ⟨f, hdep, hΨeq⟩ := hchain (2 * k + 1) hi
  obtain ⟨χ', omz, hwz, ρ, Φ, Φ₀, hΦ₀, hne⟩ := hJ

  let vW : GlobalTheory.Unf.Vol (G.V (.grid (2 * k + 1) 0)) := ⟨M.ν _, M.fd _, hhaar, hfund⟩
  obtain ⟨s, hsV, hsW, hsom, hsvW⟩ := exists_step (F.dB k h) (F.dJ k h) hw1 vW
  obtain ⟨𝒮, Γ₀, hLoc, hvacS, hbox⟩ := hGood.bf k h s hsom

  set φ : GA D (G.V (.core (2 * k + 2))) → ℂ := star (Ψ (2 * k + 2))
  set G' : GA D (G.V (.grid (2 * k + 1) 0)) → ℂ := star (part W M ρ Φ u (2 * k + 1) (by omega))
  have hφ : RapidDec _ φ := rapidDec_star (hrap (2 * k + 2) h)
  have hG' : RapidDec _ G' := rapidDec_star (hu ρ Φ (2 * k + 1) (by omega))
  have hfix : ∀ k' ∈ lev G (.grid (2 * k + 1) 0), ∀ g, G' (g * k') = G' g := fun k' hk' g =>
    congrArg star (hP D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k) (by omega) k' hk' g)

  have hvac1 : VacG W.ψ _ _ (latCore G (2 * k + 1)) (star f) := (hdepiff f).1 hdep
  obtain ⟨-, hlink⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D W.ψ W.ψ_std (negSp F.Lz) (negSp F.Lz) (G.V (.core (2 * k + 1)))
    (F.ζ (k + 1)) (F.ζ k) (F.line (k + 1)) (F.line k) (F.lnk k)
  obtain ⟨Ξ₂, hΞ₂, hΦ₀eq⟩ := hlink Φ₀ hΦ₀.1
  have hbox' := hbox (star f) Ξ₂ hvac1 hΞ₂ (by rw [← hΦ₀eq]; exact hΦ₀)

  have hlift : liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f) = star (Ψ (2 * k + 1)) := by
    rw [hΨeq]; exact (hdn v f (Ψ (2 * k + 2))).symm
  have hJper : (F.jac v k h).per W.ψ (F.ζ k) omz
      (liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f)) G'
      (fun w => star (Ξ₂ ((F.lnk k).κ _ w))) ≠ 0 := by
    rw [hlift, ← hΦ₀eq]; exact hne
  have hsχ : s.χV = (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ * L.eta := by rw [hsV, hχS]
  have hWA : IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ s.χW (omCore W (2 * k + 1)) := by
    rw [hsW, hχT]; exact hw2
  obtain ⟨Φ₁, hΦ₁S, hper₁⟩ := GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift D W.ψ k (F.bes v k h) (F.jac v k h) s 𝒮 Γ₀ _ hLoc (negSp F.Lz) (F.ζ k)
    (F.line k) (F.lnk k) _ _ χ' (omCore W (2 * k + 1)) omz hsχ hWA hwz φ G' hφ hG' hfix (star f) Ξ₂ hvac1.1 hΞ₂ hbox' hJper

  set ℓ : (WO (G.V (.grid (2 * k + 2) 0)) (G.V (.grid (2 * k + 1) 0)) → ℂ) → ℂ :=
    fun Φ' => (F.bes v k h).per W.ψ φ (liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ')
  have htame : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ vW G' hG').1 k (F.bes v k h) _ _ (omRow W (2 * k + 1)) hw1 φ hφ
  have hℓ₁ : ℓ Φ₁ ≠ 0 := by
    have e : s.lift G' Φ₁ = liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ₁ := by
      unfold GlobalTheory.Unf.Step.lift; rw [hsom, hsvW]
    rw [e] at hper₁; exact hper₁

  by_contra hall
  apply hℓ₁
  refine hF D hD T L μ0 hL sc G W M hM ⟨2 * k + 1, hi⟩ ℓ htame ?_ Φ₁ (hvacS Φ₁ hΦ₁S)
  intro κ P
  let ρ' : G.RealVec := Function.update ρ ⟨2 * k + 1, hi⟩ P
  let Φ' : G.Datum := Function.update Φ ⟨2 * k + 1, hi⟩ κ
  have hagree : ∀ j : Fin D.R.m, j.1 < 2 * k + 1 → ρ' j = ρ j ∧ Φ' j = Φ j := by
    intro j hj
    have hne' : j ≠ ⟨2 * k + 1, hi⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
    exact ⟨Function.update_of_ne hne' _ _, Function.update_of_ne hne' _ _⟩
  have hdat : W.datum ρ' Φ' ⟨2 * k + 1, hi⟩ = W.fock (.chi (2 * k + 1) 0) (W.cosVec (2 * k + 1) κ) P := by
    simp only [GlobalTheory.ChiGrid.GridData.Weil.datum, ρ', Φ', Function.update_self]
  have htop := hpart ρ' Φ' u
  rw [hpartEq ρ' Φ' ρ Φ u hagree, hdat] at htop
  have h0 : (F.bes v k h).per W.ψ φ (star (part W M ρ' Φ' u (2 * k + 1 + 1) hi)) = 0 := by
    by_contra hne0
    exact hall ⟨ρ', Φ', hne0⟩
  rw [htop] at h0
  exact h0

end GlobalTheory.AscRungB

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContractionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportLevelPlaceSymmetricChainSecondHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiFlatMapSupportFiniteCellsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapContractionSupportFinitelyManyCellsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.FinOneProof

set_option maxHeartbeats 4000000 in

theorem finOne : ∀ D : D7, FinOne D := by
  intro D ψ hstd σ S Q a
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have hFL := GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D
  have hFLs := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D hFL hFLs hOm
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D hFL hFLs hOm
  have hCo := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.T.heisenbergInvariant_factors_contraction
  obtain ⟨-, hchar, hxi, -, hcomp⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
  obtain ⟨hψc, hψ1⟩ := hchar Q.ψk Q.char
  haveI := Q.unitVol.1
  have hsd : IsSelfDual Q.ψk Q.ν := isSelfDual_of_isUnitVol Q.ν Q.cond Q.unitVol
  have hc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  obtain ⟨μV, hμV⟩ := hcomp S.s₁.χV
  obtain ⟨μW, hμW⟩ := hcomp S.s₁.χW
  obtain ⟨μV', hμV'⟩ := hcomp S.s₂.χV
  obtain ⟨μW', hμW'⟩ := hcomp S.s₂.χW
  obtain ⟨C₀, hC₀⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ (σ + 1) Q.F.s Q.F.s_ne).1 S.B Q.F.F₀).1
  obtain ⟨C₂, hC₂⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ σ (Q.F.s * (ofSplit Q.q).xi)
    (mul_ne_zero Q.F.s_ne hxi)).1 S.B' Q.F.F₂).1
  have hsb := GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective Q.k Q.ψk Q.ν hψc inferInstance
  have hjac' : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ :=
    GlobalTheory.LocMod.GSuppTwo.hz_link (ofSplit Q.q) S.l ▸ Q.F.jac

  let ca : ℂ := (((μV * μW⁻¹) (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ)
  let Φa : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) := ca • Q.Φ₁

  let cx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → ℂ := fun x => (((μV' * μW'⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)
  let Φx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x => cx x • Q.Φ₂

  have step₁ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ x, ∃ U, (ofSplit Q.q).IsModel ψ C₀ Q.F.F₁ U ∧ ∀ Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k),
        Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) →
        flatBF S.s₁ (S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) (comb ψ _ _ Q.D₁ f₁)) = U Ψ := by
    intro f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨⟨Tm, O, hTm, hO, hTO⟩, -⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₁ f₁ = Tm Q.Φ₁ := by
      rw [← hTO]; exact (Q.dat₁.2 Tm hTm O Q.Φ₁ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
      ⟨om μV⁻¹ a x Φa.1, om_mem_SB _ _ _ Φa.2⟩
    have hloc : S.s₁.om (Q.gl₀ a, Q.gl₁ x) (Tm Q.Φ₁) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil μV μW hμV hμW _ _ Q.F.G₀ Q.F.G₁ Tm hTm
        (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a) (Q.loc₁ x) Q.Φ₁ Φ' (by
          funext z; simp only [Φ', Φa, ca, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.B.V S.J.W _ _ S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁
      Tm hTm g hg h₁ hh₁
    obtain ⟨U, hU, hflat⟩ := hBF Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _
      (Q.c + 1 + 1) Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (g, h₁) * S.s₁.om (Q.gl₀ a, Q.gl₁ x) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ

  have step₂ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v), ∀ x y, ∃ U, (ofSplit Q.q).IsModel ψ Q.F.F₁ C₂ U ∧
        ∀ Ψ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k), Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1) →
        flatFB S.s₂ (S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) (comb ψ _ _ Q.D₂ f₂)) = U Ψ := by
    intro f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    obtain ⟨-, ⟨Tm, O, hTm, hO, hTO⟩⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₂ f₂ = Tm Q.Φ₂ := by
      rw [← hTO]; exact (Q.dat₂.2 Tm hTm O Q.Φ₂ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
      ⟨om μV'⁻¹ x y (Φx x).1, om_mem_SB _ _ _ (Φx x).2⟩
    have hloc : S.s₂.om (Q.gl₁ x, Q.gl₂ y) (Tm Q.Φ₂) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil μV' μW' hμV' hμW' _ _ Q.F.G₁ Q.F.G₂ Tm hTm
        (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x) (Q.loc₂ y) Q.Φ₂ Φ' (by
          funext z; simp only [Φ', Φx, cx, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.J.W S.B'.V _ _ S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂
      Tm hTm h₁ hh₁ h₂ hh₂
    obtain ⟨U, hU, hflat⟩ := hFB Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _
      (Q.c + 1) Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac' hC₂ Q.F.bes' _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (h₁, h₂) * S.s₂.om (Q.gl₁ x, Q.gl₂ y) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.fourierJacobi_flatMap_support_finite_cells Q.k Q.ψk hψc hψ1 Q.ν inferInstance Q.n₁ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1) (by omega) (by omega)
    μV⁻¹ Q.L₁.J Q.co₁.1 Φa a
  refine ⟨T₁, ?_, ?_⟩
  · intro f₁ f₂ hvac g hg h₁ hh₁ x hne
    obtain ⟨U, -, hU⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    let Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    rw [hU Ψ rfl] at hne
    have hne' : GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) ≠ 0 := by
      intro h0
      apply hne
      have : Ψ = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨β, r, hr, t, ht, j, hj, hx⟩ := hT₁ x hne'
    refine ⟨t, ht, colE (Q.c + 1 + 1) (σ + 1 + 1) β * r, ?_, j, hj, hx⟩
    exact (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.1 Q.n₁ (Q.c + 1 + 1) (σ + 1) S.J Q.F.s _ Q.F.F₁ Q.F.G₁ Q.F.jac _ β r hr
      (Q.loc₁ _)
  · intro x
    obtain ⟨T₂, hT₂⟩ := GlobalTheory.T.localFlatMapContraction_support_finitelyManyCells Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) (by omega) μV⁻¹ μV'⁻¹
      Q.L₂.J Q.co₂.1 Φa (Φx x) a x
    refine ⟨T₂, ?_⟩
    intro f₁ f₂ hvac g hg h₁ hh₁ h₂ hh₂ y hne
    obtain ⟨U₁, hU₁, hf₁⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨U₂, hU₂, hf₂⟩ := step₂ f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    let Ψ₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    let Ψ₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1) (σ + 1) (by omega)).2 (by omega)).1 _ (om_mem_SB μV'⁻¹ x y (Φx x).2)⟩
    obtain ⟨Λ, -, hΛ⟩ := hCo Q.k (ofSplit Q.q) Q.ν inferInstance ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL
      Q.F.s Q.F.s_ne _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
    obtain ⟨Ξ, hΞ, hΞΛ⟩ := hΛ Ψ₁ Ψ₂
    unfold Dbl2.con at hne
    rw [hf₁ Ψ₁ rfl, hf₂ Ψ₂ rfl, hΞΛ] at hne
    have hne' : GlobalTheory.LocFlat.contr Q.ψk Q.ν (GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1))
        (GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1)) ≠ 0 := by
      intro h0
      apply hne
      have : Ξ = 0 := Subtype.ext (hΞ.trans h0)
      rw [this, map_zero]
    obtain ⟨r, hr, t, ht, j, hj, hy⟩ := hT₂ y hne'
    exact ⟨t, ht, r, (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.2 Q.n₂ (Q.c + 1) σ S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂
      Q.F.bes' _ r hr (Q.loc₂ r), j, hj, hy⟩

end GlobalTheory.QPl.FinOneProof

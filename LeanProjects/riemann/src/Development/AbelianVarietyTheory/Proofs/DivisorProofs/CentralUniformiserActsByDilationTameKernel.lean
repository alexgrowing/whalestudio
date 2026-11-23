import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorIdempotentSumVacuumNormalisedSumStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjHalfCosetRepsScalarDilationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlacesStatement

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : GlobalTheory.ConjTwist.UnitOff N u) (hv : GlobalTheory.ConjTwist.UnitOff N v) :
    GlobalTheory.ConjTwist.UnitOff N (u * v) := by
  obtain ⟨hu0, n, h1, h2⟩ := hu
  obtain ⟨hv0, m, h3, h4⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by ring
    rw [e]; exact h1.mul h3
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [mul_inv]; ring
    rw [e]; exact h2.mul h4

theorem dilKer_of_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (lattice₂ R i) Ψ → ω (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by

  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eg eQ fg heg heQ hfg ϖ hϖ0 hϖ z hz
  obtain ⟨hSV, hSW, hθ, hfix⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hQG i hV ξ χ ξR Q ω φ hK hQt eg eQ fg heg heQ hfg
  have hW := hK.weil
  obtain ⟨hsupp, ⟨x, hx⟩, hpull, hsb, hlat⟩ :=
    GlobalTheory.T.scalarDilationElement_support_det_pullback D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  obtain ⟨Rr, hR1, hR2, hR3, hRc⟩ :=
    GlobalTheory.T.exists_conjHalf_cosetReps_scalarDilation D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  have hchi := GlobalTheory.T.twisted_splitting_character_unit_off_places D G Pl0 T0 A Ks R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  refine ⟨((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ), unitOff_mul' hchi hRc, fun Tm hTm Ψ hΨ => ?_⟩
  have hom := GlobalTheory.T.weilOperator_idempotentSum_vacuum_normalised_sum D R.ψ (Vc D i) (Wc D i) _ _ ω hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z x hsupp hx Rr hR1 hR2 hR3
    fg hθ hfix
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  have hvac : ω (z, 1) fg = (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D R.ψ (Vc D i) (Wc D i) _ _ ω hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb hvac
    Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

end GlobalTheory.BaseCmp

end

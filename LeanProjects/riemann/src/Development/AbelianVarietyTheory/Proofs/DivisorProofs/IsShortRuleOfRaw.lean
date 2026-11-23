import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BaseClassMove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.RawSpan

theorem isShortRule_of_raw : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ {n : ℕ} {Λ : GenLat E n} {N : ℕ},
    Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F},
    P ∈ harmL c Λ a → ∀ (x0 : Fin n → Dw.La) (f : Rul Xo c), f ∈ sec Xo c a n →
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (x0Dat c x0) Λ N P y (f p y)) →
    IsShortRule Xo c (GlobalTheory.RawSpan.idCover nab n) Λ N x0 P ((betaH (Dw := Dw) c Λ)⁻¹ • f) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hO a P hP x0 f hf h
  intro k _ _ i1 i2 hk y y₂ hov
  have e : i1 = i2 := (Algebra.algebra_ext _ _ fun a => hk a).symm
  subst e
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  letI : Algebra (idCover nab n).c₂.F k := i1
  have hyy : (y₂ : FrPt Xo c k) = y :=
    GlobalTheory.CoverSec.frOver_unique (idCover nab n) hL.globalFns (frOver_self nab n y₂) hov
  subst hyy
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1
  obtain ⟨p, φ, y0, h0⟩ := hAT k y₂
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) 1
  obtain ⟨v1, hv1, -⟩ := hval k y₂
  have e1 : φ (f p y0) = v1 := hnat p.R k φ y0 y₂ h0 _ _ (h p y0) hv1
  have hsm : (betaH (Dw := Dw) c Λ)⁻¹ • f ∈ sec Xo c a n := Submodule.smul_mem _ _ hf
  have e2 : evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂ = φ (((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0) :=
    GlobalTheory.CoverDescent.evR_of_test hW _ hsm.1 p φ y0 y₂ h0
  have e3 : ((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0 = algebraMap c.F p.R (betaH (Dw := Dw) c Λ)⁻¹ * f p y0 :=
    Algebra.smul_def (betaH (Dw := Dw) c Λ)⁻¹ (f p y0)
  refine ⟨evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂, ?_, ?_⟩
  · have e4 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
    rw [e4, GlobalTheory.LevelCoverDatum.noDelta_w]
    refine (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ (betaH (Dw := Dw) c Λ) hβ N P y₂ _).2 ?_
    rw [e2, e3, map_mul, AlgHom.commutes, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul, e1]
    exact hv1
  · exact ((congrArg (· * evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂) (evR_one_field k y₂)).trans (one_mul _)).symm
end GlobalTheory.RawSpan

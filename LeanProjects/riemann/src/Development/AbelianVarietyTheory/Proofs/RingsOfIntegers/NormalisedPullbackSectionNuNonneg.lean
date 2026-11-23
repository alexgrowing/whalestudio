import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueCompatibleSectionExpansionIntegralFrStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamilyStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

namespace GlobalTheory.NuPull

theorem nuGe_zero_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k N k' : ℕ) (a : 𝓞 E) (hh : SecN Xo xF k) (hh' : SecN Xo xF k'), (k = 1 ∨ 4 ≤ k) → 0 < N → a * H.bar a = (N : 𝓞 E) → k' = k * N → Pulls Xo a hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k' σ hh' → P.U.toUnifPre.ExpandsG F k' σ s → NuGe P.D Q F v k' s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl k N k' a hh hh' hk hN ha e hP h0 σ' s' ht' hs'
  letI := H.starRing
  subst e
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk₁ : 1 ≤ k := by omega
  have ha' : a * star a = (N : 𝓞 E) := ha
  have hex := GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl
  obtain ⟨⟨σ, hσ, -⟩, hu⟩ := hex k hk₁ hh
  obtain ⟨s, hs, -⟩ := hu σ hσ
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hLB : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨s'', hs''⟩ := exists_pullAl P.D F hLB P.oD H.w0 uΨ huΨ a N ha' hN k s
    (pullSecs_fe' P.D F hL.globalFns hLB P.oD H.w0 P.w0 uΨ huΨ a N ha' hN k s)
  have hE := GlobalTheory.T.normalisedPullback_section_expands_family E H Dw l Xo c T io y.1 I P F xF hσ.1 a N k (k * N) rfl ha' hN hk σ hh s σ' hh' s''
    hσ hs hP ht' hs''
  obtain rfl : s' = s'' := ((hex (k * N) (Nat.mul_pos hk₁ hN) hh').2 σ' ht').unique hs' hE
  exact (GlobalTheory.twisting_statements_of_laws hL GlobalTheory.twistBaseChange).2.2 T.V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0
    a N hN ha' (by rw [_root_.mul_comm]; exact ha') k hk₁ s s' hs'' 0 (h0 σ s hσ hs)

end GlobalTheory.NuPull

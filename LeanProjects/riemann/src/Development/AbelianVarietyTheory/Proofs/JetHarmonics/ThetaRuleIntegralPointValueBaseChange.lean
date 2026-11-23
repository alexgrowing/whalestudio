import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaRuleValue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_field_isVtOver {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) (n : ℕ) (x : Fin n → Dw.La) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra c.F F) (κ : K →ₐ[c.F] F) (z : FrPt Xo c F)
      (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x))),
      FrMap κ y z ∧
      ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (Fs b) := by
  obtain ⟨U, iU, jU, κ, u, G, hff, hu, hG⟩ :=
    exists_faithfullyFlat_isVtOver firstFiveLaws.1 E H Dw l Xo c K y n x
  have hκ : Function.Injective κ := hff.injective
  have : Nontrivial U := hκ.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal U
  let iF : Field (U ⧸ m) := Ideal.Quotient.field m
  let ψ : U →ₐ[c.F] U ⧸ m := Ideal.Quotient.mkₐ c.F m
  obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap firstFiveLaws.1 E H Dw l Xo c U (U ⧸ m) ψ u
  let h : ptO Xo z.x ⟶ ptO Xo u.x := Over.homMk (spMap ψ.toRingHom) hz.1.symm
  choose F' hF' using fun b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (G b)
  refine ⟨U ⧸ m, iF, inferInstance, ψ.comp κ, z, F', FramedBaseChange.trans κ ψ hu hz, fun b => ?_⟩
  have e : h ≫ levPt Xo u.x (x b) = levPt Xo z.x (x b) := by
    unfold levPt
    rw [← Category.assoc, comp_toUnit]
  rw [← e]
  exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) _ _ h u.s z.s
    (GlobalTheory.FramedBaseChange.isPullSec ψ hz h rfl) (G b) (F' b) (hF' b)).1 _ (hG b)

theorem map_evI_eq_thExpr (nab : NabV Xo c) (hnab : letI := H.starRing; IsNab Xo c nab) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [inst : Algebra c.F F] :
    letI := io.toAlgebra
    ∀ (κ : T.Fr →ₐ[c.F] F) (z : FrPt Xo c F), FrMap κ y.1 z →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (Fs b)) →
      ∀ f, IsThRule Xo c nab x P f → κ (evI y f) = thExpr Xo c nab z P Fs := by
  let := io.toAlgebra
  intro κ
  obtain ⟨g, hg⟩ : ∃ g : T.Fr →+* F, κ.toRingHom = g := ⟨_, rfl⟩
  have hi : inst = (g.comp io).toAlgebra := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    rw [← hg]
    exact (κ.commutes r).symm
  subst hi
  let := g.toAlgebra
  intro z hz a n x P hP Fs hF f hf
  have key := GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y F κ hg z hz a n x P hP Fs hF f hf
  exact (congrArg (fun k : T.Fr →+* F => k (evI y f)) hg).trans key

theorem evI_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io'), letI := io.toAlgebra; letI := io'.toAlgebra; ∀ φ : T.Fr →ₐ[c.F] T'.Fr, FrMap φ y.1 y'.1 → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, φ (evI y f) = evI y' f := by
  intro E _ _ _ H Dw l Xo c nab hnab T T' io io' y y' φ hφ a n f hf
  let := io.toAlgebra
  let := io'.toAlgebra
  obtain ⟨x, P, hP, hf⟩ := hf
  obtain ⟨F, iF, jF, κ, z, Fs, hz, hF⟩ := exists_field_isVtOver y'.1 n x
  apply κ.toRingHom.injective
  have h₁ := map_evI_eq_thExpr nab hnab T io y F (κ.comp φ) z (FramedBaseChange.trans φ κ hφ hz)
    a n x P hP Fs hF f hf
  have h₂ := map_evI_eq_thExpr nab hnab T' io' y' F κ z hz a n x P hP Fs hF f hf
  exact h₁.trans h₂.symm

end GlobalTheory.ThetaRuleValue
